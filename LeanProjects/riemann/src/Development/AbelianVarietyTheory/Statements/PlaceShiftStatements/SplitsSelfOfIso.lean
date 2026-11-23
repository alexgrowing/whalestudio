import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.IdTower

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.GalV

def VFin : Prop := ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k], IsUnit (l : k) → ∀ {X : Scheme.{0}}
  (p : X ⟶ Spec (CommRingCat.of k)) [IsProper p] (n i : ℤ),
  Module.Finite ℤ_[l] (Hl l (sch.obj X) n i) ∧ FiniteDimensional ℚ_[l] (HQ l (sch.obj X) n i)

def VCont : Prop := ∀ (l : ℕ) [Fact l.Prime] (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [Algebra.IsAlgebraic k Ω], IsUnit (l : k) →
  ∀ {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) [QuasiCompact p] [QuasiSeparated p] (n i : ℤ),
  Module.Finite ℤ_[l] (Hl l (sch.obj (GlobalTheory.Et.geom Ω p)) n i) →
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℚ_[l] (HQ l (sch.obj (GlobalTheory.Et.geom Ω p)) n i)),
    Continuous fun σ : Ω ≃ₐ[k] Ω => LinearMap.toMatrix b b (galHQ l Ω p n i σ)

def VInv : Prop := ∀ (l : ℕ) [Fact l.Prime] {Y X : Scheme.{0}} (f : Y ⟶ X) [IsFinite f] [Etale f] [Surjective f] (G : Type) [Fintype G]
  (a : G → (Y ⟶ Y)) (ha : ∀ g, a g ≫ f = f),
  IsIso (Sigma.desc (fun g => pullback.lift (a g) (𝟙 Y) (by rw [ha g, Category.id_comp])) : ∐ (fun _ : G => Y) ⟶ pullback f f) → ∀ n i : ℤ, Function.Injective (pullHQ l (sch.map f) n i) ∧
  LinearMap.range (pullHQ l (sch.map f) n i) = ⨅ g, LinearMap.ker (pullHQ l (sch.map (a g)) n i - LinearMap.id)

def VIso : Prop := ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k], IsUnit (l : k) → ∀ {X Y : Scheme.{0}}
  (p : X ⟶ Spec (CommRingCat.of k)) (q : Y ⟶ Spec (CommRingCat.of k)) [IsProper p] [IsProper q]
  (f : Y ⟶ X) (g : X ⟶ Y) [IsFinite f] [Etale f] [Surjective f] [IsFinite g] [Etale g] [Surjective g] (d e : ℕ),
  (∃ (U : Scheme.{0}) (u : U ⟶ X), Etale u ∧ Surjective u ∧ ∃ e : ∐ (fun _ : Fin d => U) ≅ pullback f u, e.hom ≫ pullback.snd f u = Limits.Sigma.desc (fun _ => 𝟙 U)) → (∃ (U : Scheme.{0}) (u : U ⟶ Y), Etale u ∧ Surjective u ∧ ∃ e : ∐ (fun _ : Fin e => U) ≅ pullback g u, e.hom ≫ pullback.snd g u = Limits.Sigma.desc (fun _ => 𝟙 U)) → ∀ n i : ℤ, Function.Bijective (pullHQ l (sch.map f) n i)

def VBc : Prop := ∀ (l : ℕ) [Fact l.Prime] (k Ω : Type) [Field k] [IsAlgClosed k] [Field Ω] [IsAlgClosed Ω] [Algebra k Ω], IsUnit (l : k) →
  ∀ {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) [IsProper p] (n i : ℤ),
  Function.Bijective (pullHQ l (sch.map (pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k Ω))))) n i)

def VGal : Prop := ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] (H : HTower k) (Ω : Type) [Field Ω] [Algebra k Ω] (g : H.Γ),
  (∃ T, IsCorrOp l (H.sΩ Ω g) (H.tΩ Ω g) T) → ∀ σ : Ω ≃ₐ[k] Ω,
    hop l H Ω g ∘ₗ galTot l Ω H.q σ = galTot l Ω H.q σ ∘ₗ hop l H Ω g ∧
    ∀ (L : Type) [Field L] [Algebra ℚ_[l] L] {J : Type} (ι : J → H.Γ) (θ : J → L),
      (∀ j, ∃ T, IsCorrOp l (H.sΩ Ω (ι j)) (H.tΩ Ω (ι j)) T) → ∀ x ∈ V l H Ω L ι θ, galV l H Ω L σ x ∈ V l H Ω L ι θ

def VTop : Prop := VFin ∧ VCont ∧ VInv ∧ VIso ∧ VBc ∧ VGal

end GlobalTheory.GalV

namespace GlobalTheory.GalV.GaloisTowerConditions

variable {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω]

theorem geomMap_isIso {X Y : Scheme.{0}} {p : X ⟶ Spec (CommRingCat.of k)} {q : Y ⟶ Spec (CommRingCat.of k)}
    (u : X ⟶ Y) [IsIso u] (hu : u ≫ q = p) : IsIso (GlobalTheory.Et.geomMap Ω p u hu) := by
  refine ⟨⟨GlobalTheory.Et.geomMap Ω q (inv u) (by simp [← hu]), ?_, ?_⟩⟩
  · apply pullback.hom_ext
    · simp only [GlobalTheory.Et.geomMap, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, IsIso.hom_inv_id, Category.comp_id, Category.id_comp]
    · simp only [GlobalTheory.Et.geomMap, Category.assoc, pullback.lift_snd, Category.id_comp]
  · apply pullback.hom_ext
    · simp only [GlobalTheory.Et.geomMap, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, IsIso.inv_hom_id, Category.comp_id, Category.id_comp]
    · simp only [GlobalTheory.Et.geomMap, Category.assoc, pullback.lift_snd, Category.id_comp]

instance isIso_idTower_sΩ (g : (HTower.idTower k).Γ) : IsIso ((HTower.idTower k).sΩ Ω g) :=
  geomMap_isIso Ω (k := k) (𝟙 _) rfl

theorem splits_self_of_iso {Y Z : Scheme.{0}} (s : Y ⟶ Z) [IsIso s] : Splits s s (fun _ : Unit => 𝟙 Y) := by
  refine ⟨fun _ => Category.id_comp _, ?_⟩
  have hl : IsIso (pullback.lift (𝟙 Y) (𝟙 Y) (by simp) : Y ⟶ pullback s s) := by
    have : IsIso (pullback.lift (𝟙 Y) (𝟙 Y) (by simp) ≫ pullback.fst s s) := by
      rw [pullback.lift_fst]; infer_instance
    exact IsIso.of_isIso_comp_right _ (pullback.fst _ _)
  refine ⟨⟨inv (pullback.lift (𝟙 Y) (𝟙 Y) rfl : Y ⟶ pullback s s) ≫ Sigma.ι (fun _ : Unit => Y) (), ?_, ?_⟩⟩
  · apply Sigma.hom_ext; intro j; cases j; simp
  · simp

theorem idTower_isCorrOp (l : ℕ) [Fact l.Prime] (g : (HTower.idTower k).Γ) :
    IsCorrOp l ((HTower.idTower k).sΩ Ω g) ((HTower.idTower k).tΩ Ω g) LinearMap.id := by
  refine ⟨_, (HTower.idTower k).sΩ Ω g, Unit, inferInstance, inferInstance, fun _ => 𝟙 _, Unit, inferInstance,
    fun _ => 𝟙 _, ⟨inferInstance, inferInstance, inferInstance, rfl, fun _ _ => (Category.id_comp _).symm,
      splits_self_of_iso _⟩, splits_self_of_iso _, fun x => ?_⟩
  simp only [LinearMap.id_apply, Finset.univ_unique, Finset.sum_singleton, Category.id_comp]
  rfl

example (l : ℕ) [Fact l.Prime] (g : (HTower.idTower k).Γ) :
    ∃ T, IsCorrOp l ((HTower.idTower k).sΩ Ω g) ((HTower.idTower k).tΩ Ω g) T := ⟨_, idTower_isCorrOp Ω l g⟩

theorem cohomology_invariants_identity_cover (l : ℕ) [Fact l.Prime] (X : Scheme.{0}) (n i : ℤ) :
    IsIso (Sigma.desc (fun g : Unit => pullback.lift ((fun _ : Unit => 𝟙 X) g) (𝟙 X) (by simp)) :
      ∐ (fun _ : Unit => X) ⟶ pullback (𝟙 X) (𝟙 X)) ∧
    (Function.Injective (pullHQ l (sch.map (𝟙 X)) n i) ∧
      LinearMap.range (pullHQ l (sch.map (𝟙 X)) n i) =
        ⨅ g : Unit, LinearMap.ker (pullHQ l (sch.map ((fun _ : Unit => 𝟙 X) g)) n i - LinearMap.id)) := by
  have hid : pullHQ l (sch.map (𝟙 X)) n i = LinearMap.id := by
    rw [CategoryTheory.Functor.map_id]; unfold pullHQ; rw [pullHl_id]; exact LinearMap.baseChange_id
  refine ⟨(splits_self_of_iso (𝟙 X)).2, ?_⟩
  simp only [hid, sub_self, LinearMap.ker_zero, iInf_const, LinearMap.range_id]
  exact ⟨Function.injective_id, trivial⟩

end GlobalTheory.GalV.GaloisTowerConditions

end
