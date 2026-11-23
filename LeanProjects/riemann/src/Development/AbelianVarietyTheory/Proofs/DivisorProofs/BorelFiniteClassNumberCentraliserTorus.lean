import Mathlib
import Formalism.UnipotentAdelicQuotients.ClassNumberFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormGroupToPadicPointsDegreeOneEqUnitaryPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDoubleCosetAwayP
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsClosedZeroLocusGL

noncomputable section

open NumberField GlobalTheory.LKTrip
open scoped TensorProduct

namespace GlobalTheory.TorCls.Borel

variable {N : ℕ} {S : Set (MvPolynomial (Fin N × Fin N) ℚ)} (hS : HeckeCharacterZeroLocus.IsGroupLocus S)

theorem aeval_map_entries {R R' : Type} [CommRing R] [Algebra ℚ R] [CommRing R'] [Algebra ℚ R']
    (f : R →ₐ[ℚ] R') (M : Matrix (Fin N) (Fin N) R) (P : MvPolynomial (Fin N × Fin N) ℚ) :
    MvPolynomial.aeval (fun ij : Fin N × Fin N => f (M ij.1 ij.2)) P =
      f (MvPolynomial.aeval (fun ij : Fin N × Fin N => M ij.1 ij.2) P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

theorem mem_locus_map {R R' : Type} [CommRing R] [Algebra ℚ R] [CommRing R'] [Algebra ℚ R'] (f : R →ₐ[ℚ] R')
    (g : HeckeCharacterZeroLocus.locusSubgroup S hS R) :
    Units.map (f.toRingHom.mapMatrix : Matrix (Fin N) (Fin N) R →+* Matrix (Fin N) (Fin N) R').toMonoidHom
      (g : GL (Fin N) R) ∈ HeckeCharacterZeroLocus.locusSubgroup S hS R' := by
  intro P hP
  have h := g.2 P hP
  show MvPolynomial.aeval (fun ij : Fin N × Fin N => f (((g : GL (Fin N) R) : Matrix (Fin N) (Fin N) R) ij.1 ij.2)) P = 0
  rw [aeval_map_entries, h, map_zero]

def locMap {R R' : Type} [CommRing R] [Algebra ℚ R] [CommRing R'] [Algebra ℚ R'] (f : R →ₐ[ℚ] R') :
    HeckeCharacterZeroLocus.locusSubgroup S hS R →* HeckeCharacterZeroLocus.locusSubgroup S hS R' :=
  ((Units.map (f.toRingHom.mapMatrix : Matrix (Fin N) (Fin N) R →+* Matrix (Fin N) (Fin N) R').toMonoidHom).comp
    (HeckeCharacterZeroLocus.locusSubgroup S hS R).subtype).codRestrict _ (mem_locus_map hS f)

theorem locMap_comp {R R' R'' : Type} [CommRing R] [Algebra ℚ R] [CommRing R'] [Algebra ℚ R']
    [CommRing R''] [Algebra ℚ R''] (f : R' →ₐ[ℚ] R'') (f' : R →ₐ[ℚ] R') (g : HeckeCharacterZeroLocus.locusSubgroup S hS R) :
    locMap hS f (locMap hS f' g) = locMap hS (f.comp f') g := rfl

theorem continuous_locMap {R R' : Type} [CommRing R] [Algebra ℚ R] [TopologicalSpace R] [CommRing R']
    [Algebra ℚ R'] [TopologicalSpace R'] (f : R →ₐ[ℚ] R') (hf : Continuous f) :
    Continuous (locMap hS f) := by
  refine Continuous.subtype_mk ?_ _
  refine (Continuous.units_map _ ?_).comp continuous_subtype_val
  exact Continuous.matrix_map continuous_id hf

theorem lid_starT {D : Type} [Ring D] [Algebra ℚ D] (σ : D →+* Dᵐᵒᵖ) (x : ℚ ⊗[ℚ] D) :
    Algebra.TensorProduct.lid ℚ D (starT σ ℚ x).unop = (σ (Algebra.TensorProduct.lid ℚ D x)).unop := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul q d =>
    rw [starT_tmul, Algebra.TensorProduct.lid_tmul, Algebra.TensorProduct.lid_tmul, map_rat_smul,
      MulOpposite.unop_smul]
  | add x y hx hy => simp only [map_add, MulOpposite.unop_add, hx, hy]

theorem map_ofId_eq {D B : Type} [Ring D] [Algebra ℚ D] [CommRing B] [Algebra ℚ B] (x : ℚ ⊗[ℚ] D) :
    Algebra.TensorProduct.map (Algebra.ofId ℚ B) (AlgHom.id ℚ D) x =
      (Algebra.TensorProduct.includeRight : D →ₐ[ℚ] B ⊗[ℚ] D) (Algebra.TensorProduct.lid ℚ D x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul q d =>
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lid_tmul, Algebra.TensorProduct.includeRight_apply,
      TensorProduct.tmul_smul, TensorProduct.smul_tmul', AlgHom.id_apply, Algebra.ofId_apply,
      Algebra.algebraMap_eq_smul_one]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem tc_rat {D : Type} [Ring D] [Algebra ℚ D] (σ : D →+* Dᵐᵒᵖ) (β y : D) (z : (ℚ ⊗[ℚ] D)ˣ × ℚˣ)
    (h : GlobalTheory.TorCls.TC D σ β y ℚ z) :
    Algebra.TensorProduct.lid ℚ D (z.1 : ℚ ⊗[ℚ] D) * β * (σ (Algebra.TensorProduct.lid ℚ D (z.1 : ℚ ⊗[ℚ] D))).unop =
        algebraMap ℚ D (z.2 : ℚ) * β ∧
      Commute (Algebra.TensorProduct.lid ℚ D (z.1 : ℚ ⊗[ℚ] D)) y := by
  obtain ⟨h1, h2⟩ := h
  constructor
  · have := congrArg (Algebra.TensorProduct.lid ℚ D) h1
    simp only [map_mul, lid_starT] at this
    simpa [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_eq_smul_one] using this
  · have := h2.map (Algebra.TensorProduct.lid ℚ D)
    simpa using this

end GlobalTheory.TorCls.Borel

namespace GlobalTheory.TorCls.Borel

open IsDedekindDomain

theorem classes_finite : (∀ (D : Type) [Ring D] [Algebra ℚ D] [FiniteDimensional ℚ D] (σ : D →+* Dᵐᵒᵖ) (β y : D),
  ∃ (N : ℕ) (S : Set (MvPolynomial (Fin N × Fin N) ℚ)) (hS : HeckeCharacterZeroLocus.IsGroupLocus S)
    (φ : ∀ (R : Type) [CommRing R] [Algebra ℚ R], HeckeCharacterZeroLocus.locusSubgroup S hS R →* (R ⊗[ℚ] D)ˣ × Rˣ),
    (∀ (R : Type) [CommRing R] [Algebra ℚ R], Function.Injective (φ R) ∧
      ∀ z : (R ⊗[ℚ] D)ˣ × Rˣ, GlobalTheory.TorCls.TC D σ β y R z ↔ z ∈ Set.range (φ R)) ∧
    (∀ (R R' : Type) [CommRing R] [Algebra ℚ R] [CommRing R'] [Algebra ℚ R'] (f : R →ₐ[ℚ] R')
      (g : HeckeCharacterZeroLocus.locusSubgroup S hS R) (g' : HeckeCharacterZeroLocus.locusSubgroup S hS R'),
      (g' : GL (Fin N) R') = Units.map (f.toRingHom.mapMatrix : Matrix (Fin N) (Fin N) R →+* Matrix (Fin N) (Fin N) R').toMonoidHom (g : GL (Fin N) R) →
      φ R' g' = (Units.map (Algebra.TensorProduct.map f (AlgHom.id ℚ D)).toRingHom.toMonoidHom (φ R g).1,
        Units.map f.toRingHom.toMonoidHom (φ R g).2)) ∧
    (∀ (R : Type) [CommRing R] [Algebra ℚ R] [TopologicalSpace R] [IsTopologicalRing R],
      letI : TopologicalSpace (R ⊗[ℚ] D) := moduleTopology R (R ⊗[ℚ] D)
      Continuous (φ R))) → HeckeCharacterZeroLocus.ClassNumberFinite → ∀ (D : Type) [Ring D] [Algebra ℚ D] [FiniteDimensional ℚ D] (σ : D →+* Dᵐᵒᵖ) (β y : D) (p : ℕ) [Fact p.Prime],
    letI : TopologicalSpace (AfP p ⊗[ℚ] D) := moduleTopology (AfP p) (AfP p ⊗[ℚ] D)
    letI : TopologicalSpace (ℚ_[p] ⊗[ℚ] D) := moduleTopology ℚ_[p] (ℚ_[p] ⊗[ℚ] D)
    ∀ U : Subgroup (((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ)),
      (∃ O : Set (((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ)), IsOpen O ∧ 1 ∈ O ∧
        ∀ z ∈ O, GlobalTheory.TorCls.TC D σ β y (AfP p) z.1 → GlobalTheory.TorCls.TC D σ β y ℚ_[p] z.2 → z ∈ U) →
      ∃ S : Finset (((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ)),
        ∀ z, GlobalTheory.TorCls.TC D σ β y (AfP p) z.1 → GlobalTheory.TorCls.TC D σ β y ℚ_[p] z.2 →
          ∃ γ : Dˣ × ℚˣ, (γ.1 : D) * β * (σ γ.1).unop = algebraMap ℚ D γ.2 * β ∧ Commute (γ.1 : D) y ∧
            ∃ s ∈ S, ∃ u ∈ U, z = GlobalTheory.TorCls.dg D p γ * s * u := by
  intro hbr hB D _ _ _ σ β y p _
  obtain ⟨N, S, hS, φ, hiso, hnat, hcont⟩ := hbr D σ β y
  letI : TopologicalSpace (AfP p ⊗[ℚ] D) := moduleTopology (AfP p) (AfP p ⊗[ℚ] D)
  letI : TopologicalSpace (ℚ_[p] ⊗[ℚ] D) := moduleTopology ℚ_[p] (ℚ_[p] ⊗[ℚ] D)
  intro U hUO
  obtain ⟨O, hO, h1O, hOU⟩ := hUO
  obtain ⟨π₁, π₂, hc₁, hc₂, hbij⟩ := GlobalTheory.CentTorus.AdelicSplit.adele_split p
  let Φ : HeckeCharacterZeroLocus.locusSubgroup S hS (FiniteAdeleRing (𝓞 ℚ) ℚ) →*
      ((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ) :=
    ((φ (AfP p)).comp (locMap hS π₁)).prod ((φ ℚ_[p]).comp (locMap hS π₂))
  have hφ₁ : Continuous (φ (AfP p)) := hcont (AfP p)
  have hφ₂ : Continuous (φ ℚ_[p]) := hcont ℚ_[p]
  have hΦc : Continuous Φ :=
    (hφ₁.comp (continuous_locMap hS π₁ hc₁)).prodMk (hφ₂.comp (continuous_locMap hS π₂ hc₂))
  have hTC : ∀ g, GlobalTheory.TorCls.TC D σ β y (AfP p) (Φ g).1 ∧ GlobalTheory.TorCls.TC D σ β y ℚ_[p] (Φ g).2 := fun g =>
    ⟨((hiso (AfP p)).2 _).2 ⟨_, rfl⟩, ((hiso ℚ_[p]).2 _).2 ⟨_, rfl⟩⟩

  have hsurj : ∀ z : ((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ),
      GlobalTheory.TorCls.TC D σ β y (AfP p) z.1 → GlobalTheory.TorCls.TC D σ β y ℚ_[p] z.2 → ∃ g, Φ g = z := by
    intro z h1 h2
    obtain ⟨g₁, hg₁⟩ := ((hiso (AfP p)).2 z.1).1 h1
    obtain ⟨g₂, hg₂⟩ := ((hiso ℚ_[p]).2 z.2).1 h2
    let s := Function.surjInv hbij.2
    have hs : ∀ x, (π₁ (s x), π₂ (s x)) = x := Function.surjInv_eq hbij.2
    have hs₁ : ∀ a b, π₁ (s (a, b)) = a := fun a b => congrArg Prod.fst (hs (a, b))
    have hs₂ : ∀ a b, π₂ (s (a, b)) = b := fun a b => congrArg Prod.snd (hs (a, b))
    have hinj : ∀ a a' : FiniteAdeleRing (𝓞 ℚ) ℚ, π₁ a = π₁ a' → π₂ a = π₂ a' → a = a' :=
      fun a a' h h' => hbij.1 (Prod.ext h h')
    have hinjM : ∀ X Y : Matrix (Fin N) (Fin N) (FiniteAdeleRing (𝓞 ℚ) ℚ),
        π₁.toRingHom.mapMatrix X = π₁.toRingHom.mapMatrix Y →
        π₂.toRingHom.mapMatrix X = π₂.toRingHom.mapMatrix Y → X = Y := by
      intro X Y h h'
      refine Matrix.ext fun i j => ?_
      exact hinj _ _ (congrFun (congrFun h i) j) (congrFun (congrFun h' i) j)
    let G₁ : GL (Fin N) (AfP p) := g₁
    let G₂ : GL (Fin N) ℚ_[p] := g₂
    let M : Matrix (Fin N) (Fin N) (FiniteAdeleRing (𝓞 ℚ) ℚ) :=
      Matrix.of fun i j => s ((G₁ : Matrix (Fin N) (Fin N) (AfP p)) i j, (G₂ : Matrix (Fin N) (Fin N) ℚ_[p]) i j)
    let M' : Matrix (Fin N) (Fin N) (FiniteAdeleRing (𝓞 ℚ) ℚ) :=
      Matrix.of fun i j => s (((G₁⁻¹ : GL (Fin N) (AfP p)) : Matrix (Fin N) (Fin N) (AfP p)) i j,
        ((G₂⁻¹ : GL (Fin N) ℚ_[p]) : Matrix (Fin N) (Fin N) ℚ_[p]) i j)
    have hM₁ : π₁.toRingHom.mapMatrix M = (G₁ : Matrix (Fin N) (Fin N) (AfP p)) := by
      ext i j; exact hs₁ _ _
    have hM₂ : π₂.toRingHom.mapMatrix M = (G₂ : Matrix (Fin N) (Fin N) ℚ_[p]) := by
      ext i j; exact hs₂ _ _
    have hM'₁ : π₁.toRingHom.mapMatrix M' = ((G₁⁻¹ : GL (Fin N) (AfP p)) : Matrix (Fin N) (Fin N) (AfP p)) := by
      ext i j; exact hs₁ _ _
    have hM'₂ : π₂.toRingHom.mapMatrix M' = ((G₂⁻¹ : GL (Fin N) ℚ_[p]) : Matrix (Fin N) (Fin N) ℚ_[p]) := by
      ext i j; exact hs₂ _ _
    have hMM' : M * M' = 1 := hinjM _ _ (by rw [map_mul, map_one, hM₁, hM'₁]; simp)
      (by rw [map_mul, map_one, hM₂, hM'₂]; simp)
    have hM'M : M' * M = 1 := hinjM _ _ (by rw [map_mul, map_one, hM₁, hM'₁]; simp)
      (by rw [map_mul, map_one, hM₂, hM'₂]; simp)
    let G : GL (Fin N) (FiniteAdeleRing (𝓞 ℚ) ℚ) := ⟨M, M', hMM', hM'M⟩
    have hG : G ∈ HeckeCharacterZeroLocus.locusSubgroup S hS (FiniteAdeleRing (𝓞 ℚ) ℚ) := by
      intro P hP
      apply hinj
      · rw [map_zero, ← aeval_map_entries]
        have e : (fun ij : Fin N × Fin N => π₁ ((G : Matrix (Fin N) (Fin N) (FiniteAdeleRing (𝓞 ℚ) ℚ)) ij.1 ij.2)) =
            fun ij => (G₁ : Matrix (Fin N) (Fin N) (AfP p)) ij.1 ij.2 := by
          funext ij; exact hs₁ _ _
        rw [e]; exact g₁.2 P hP
      · rw [map_zero, ← aeval_map_entries]
        have e : (fun ij : Fin N × Fin N => π₂ ((G : Matrix (Fin N) (Fin N) (FiniteAdeleRing (𝓞 ℚ) ℚ)) ij.1 ij.2)) =
            fun ij => (G₂ : Matrix (Fin N) (Fin N) ℚ_[p]) ij.1 ij.2 := by
          funext ij; exact hs₂ _ _
        rw [e]; exact g₂.2 P hP
    refine ⟨⟨G, hG⟩, Prod.ext ?_ ?_⟩
    · show φ (AfP p) (locMap hS π₁ ⟨G, hG⟩) = z.1
      rw [← hg₁]; congr 1; apply Subtype.ext; apply Units.ext; exact hM₁
    · show φ ℚ_[p] (locMap hS π₂ ⟨G, hG⟩) = z.2
      rw [← hg₂]; congr 1; apply Subtype.ext; apply Units.ext; exact hM₂

  let U' : Subgroup (HeckeCharacterZeroLocus.locusSubgroup S hS (FiniteAdeleRing (𝓞 ℚ) ℚ)) := U.comap Φ
  have hU'o : IsOpen (U' : Set (HeckeCharacterZeroLocus.locusSubgroup S hS (FiniteAdeleRing (𝓞 ℚ) ℚ))) := by
    apply Subgroup.isOpen_of_mem_nhds U' (g := 1)
    have h1 : (1 : HeckeCharacterZeroLocus.locusSubgroup S hS (FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ Φ ⁻¹' O := by
      show Φ 1 ∈ O; rw [map_one]; exact h1O
    refine Filter.mem_of_superset ((hO.preimage hΦc).mem_nhds h1) ?_
    intro g hg
    exact hOU _ hg (hTC g).1 (hTC g).2
  have hU'c : IsClosed (U' : Set (HeckeCharacterZeroLocus.locusSubgroup S hS (FiniteAdeleRing (𝓞 ℚ) ℚ))) :=
    U'.isClosed_of_isOpen hU'o
  obtain ⟨K, hKo, hKc⟩ := GlobalTheory.LocusOpenCompact.exists_isOpen_isCompact ℚ N S hS
  obtain ⟨T₀, hT₀⟩ := hB ℚ N S hS (U' ⊓ K) (by rw [Subgroup.coe_inf]; exact hU'o.inter hKo)
    (by
      rw [Subgroup.coe_inf]
      exact hKc.inter_left hU'c)

  classical
  refine ⟨T₀.image Φ, ?_⟩
  intro z h1 h2
  obtain ⟨g, rfl⟩ := hsurj z h1 h2
  obtain ⟨γ, hγ, s, hs, u, hu, hx⟩ := hT₀ g
  let γL : HeckeCharacterZeroLocus.locusSubgroup S hS ℚ := ⟨γ, hγ⟩
  have hg : g = locMap hS (Algebra.ofId ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)) γL * s * u := Subtype.ext hx
  let w := φ ℚ γL
  have hw : GlobalTheory.TorCls.TC D σ β y ℚ w := ((hiso ℚ).2 w).2 ⟨γL, rfl⟩
  obtain ⟨hw1, hw2⟩ := tc_rat σ β y w hw
  let γ' : Dˣ × ℚˣ :=
    (Units.map (Algebra.TensorProduct.lid ℚ D).toAlgHom.toRingHom.toMonoidHom w.1, w.2)
  have hcomp₁ : π₁.comp (Algebra.ofId ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)) = Algebra.ofId ℚ (AfP p) :=
    AlgHom.ext fun q => by simp
  have hcomp₂ : π₂.comp (Algebra.ofId ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)) = Algebra.ofId ℚ ℚ_[p] :=
    AlgHom.ext fun q => by simp
  have hΦγ : Φ (locMap hS (Algebra.ofId ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)) γL) = GlobalTheory.TorCls.dg D p γ' := by
    refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)
    · show (φ (AfP p) (locMap hS π₁ (locMap hS _ γL))).1 = _
      rw [locMap_comp, hcomp₁, hnat ℚ (AfP p) (Algebra.ofId ℚ (AfP p)) γL _ rfl]
      apply Units.ext
      exact map_ofId_eq _
    · show (φ (AfP p) (locMap hS π₁ (locMap hS _ γL))).2 = _
      rw [locMap_comp, hcomp₁, hnat ℚ (AfP p) (Algebra.ofId ℚ (AfP p)) γL _ rfl]
      rfl
    · show (φ ℚ_[p] (locMap hS π₂ (locMap hS _ γL))).1 = _
      rw [locMap_comp, hcomp₂, hnat ℚ ℚ_[p] (Algebra.ofId ℚ ℚ_[p]) γL _ rfl]
      apply Units.ext
      exact map_ofId_eq _
    · show (φ ℚ_[p] (locMap hS π₂ (locMap hS _ γL))).2 = _
      rw [locMap_comp, hcomp₂, hnat ℚ ℚ_[p] (Algebra.ofId ℚ ℚ_[p]) γL _ rfl]
      rfl
  refine ⟨γ', hw1, hw2, Φ s, Finset.mem_image_of_mem _ hs, Φ u, (Subgroup.mem_inf.1 hu).1, ?_⟩
  rw [hg, map_mul, map_mul, hΦγ]

end GlobalTheory.TorCls.Borel
