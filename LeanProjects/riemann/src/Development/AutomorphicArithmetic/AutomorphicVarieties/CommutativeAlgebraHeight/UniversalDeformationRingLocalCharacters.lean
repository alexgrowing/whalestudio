import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FinDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.UnivLift
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.UnivCond
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoRes
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LocallyConstantOfKernel

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private def toMat {G R : Type} [Group G] [CommRing R] (ψ : G →* Rˣ) : G →* Matrix Unit Unit R where
  toFun g := Matrix.of fun _ _ => (ψ g : R)
  map_one' := by ext a b; simp
  map_mul' g h := by ext a b; simp [Matrix.mul_apply]

private noncomputable def ofMat {G R : Type} [Group G] [CommRing R] (ρ : G →* Matrix Unit Unit R) : G →* Rˣ :=
  MonoidHom.toHomUnits
    { toFun := fun g => ρ g () ()
      map_one' := by simp
      map_mul' := fun g h => by simp [Matrix.mul_apply] }

private theorem lc_of_open {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H]
    (f : G →* H) (h : IsOpen (f.ker : Set G)) : IsLocallyConstant f :=
  _root_.UpperTheory.Reformulated.B.LocallyConstantOfKernel.lc_of_ker f h

private theorem eq_one_of_pow {k : Type} [Field k] (l : ℕ) [Fact l.Prime] [CharP k l] (x : k) (m : ℕ)
    (h : x ^ l ^ m = 1) : x = 1 := by
  have h2 : (x - 1) ^ l ^ m = 0 := by rw [sub_pow_char_pow, h]; simp
  exact sub_eq_zero.1 (pow_eq_zero_iff (pow_ne_zero m (Fact.out : l.Prime).ne_zero) |>.1 h2)

private theorem psib_th {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O]
    [CharP (ResidueField O) l] [Algebra ℤ_[l] O] {n : ℕ} (r : Resid F O n) (v : F.Vl) (i : Fin n) (g : F.mu v) :
    ((r.psib v i g : (ResidueField O)ˣ) : ResidueField O) = residue O (r.th v i g) := by
  obtain ⟨m, hm⟩ := (CommGroup.primaryComponent.isPGroup (G := TopologicalAbelianization (F.Gv v)) (p := l))
    ⟨QuotientGroup.mk' _ (g : F.Gv v), g.2⟩
  have h1 : (QuotientGroup.mk' (commutator (F.Gv v)).topologicalClosure ((g : F.Gv v) ^ l ^ m)) = 1 := by
    rw [map_pow]; exact congrArg Subtype.val hm
  have h2 : (g : F.Gv v) ^ l ^ m ∈ (commutator (F.Gv v)).topologicalClosure := (QuotientGroup.eq_one_iff _).1 h1
  have h3 : (commutator (F.Gv v)).topologicalClosure ≤ (r.psib v i).ker :=
    Subgroup.topologicalClosure_minimal _ (Abelianization.commutator_subset_ker _)
      (Subgroup.isClosed_of_isOpen _ (r.psib_open v i))
  have h4 : r.psib v i g ^ l ^ m = 1 := by rw [← map_pow]; exact h3 h2
  have h5 : r.th v i g ^ l ^ m = 1 := by rw [← map_pow]; exact r.th_comm v i _ h2
  rw [eq_one_of_pow l ((r.psib v i g : (ResidueField O)ˣ) : ResidueField O) m
      (by rw [← Units.val_pow_eq_pow_val, h4, Units.val_one]),
    eq_one_of_pow l (residue O (r.th v i g)) m
      (by rw [← map_pow, ← Units.val_pow_eq_pow_val, h5, Units.val_one, map_one])]

theorem UpperTheory.V.CA.universalDeformationRing_localCharacters :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] [CharP (ResidueField O) l] [Algebra ℤ_[l] O] {n : ℕ} (r : Resid F O n) (v : F.Vl) (i : Fin n), PhiCond (F.Gv v) l → ∃ (R : Type) (_ : CommRing R) (_ : Algebra O R) (_ : IsCO O R) (ψ : F.Gv v →* Rˣ), r.IsPsi v i ψ ∧ ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (ψ' : F.Gv v →* R'ˣ), r.IsPsi v i ψ' → ∃! f : R →ₐ[O] R', pushCh (f : R →+* R') ψ = ψ' := by
  intro l _ F O _ _ _ _ _ _ _ n r v i hΦ
  have hlc : IsLocallyConstant (r.psib v i) := lc_of_open _ (r.psib_open v i)
  have hlc' : IsLocallyConstant (toMat (r.psib v i)) :=
    hlc.comp fun x => (Matrix.of fun _ _ => (x : ResidueField O) : Matrix Unit Unit (ResidueField O))
  obtain ⟨R₀, _, _, _, u, hu⟩ := univ_lift l O (F.Gv v) Unit (toMat (r.psib v i)) hΦ hlc'
  let P : Cond O (toMat (r.psib v i)) := fun R _ _ _ s =>
    ∀ g : F.mu v, s.hom g () () = algebraMap O R (r.th v i g)
  have hP : P.IsClosed := fun R _ _ _ s => by
    refine ⟨Ideal.span (Set.range fun g : F.mu v => s.hom g () () - algebraMap O R (r.th v i g)),
      fun R' _ _ _ f => ⟨fun h x hx => ?_, fun h g => ?_⟩⟩
    · have : Ideal.span (Set.range fun g : F.mu v => s.hom g () () - algebraMap O R (r.th v i g)) ≤
          RingHom.ker f := by
        rw [Ideal.span_le]
        rintro _ ⟨g, rfl⟩
        show f _ = 0
        rw [map_sub, AlgHom.commutes, sub_eq_zero]
        exact h g
      exact this hx
    · have := h _ (Ideal.subset_span ⟨g, rfl⟩)
      rwa [map_sub, AlgHom.commutes, sub_eq_zero] at this
  haveI := (co_res O).1
  have hres : ∀ x : ResidueField O, res O (ResidueField O) x = x := fun x => by
    obtain ⟨a, rfl⟩ := residue_surjective x
    exact (res O (ResidueField O)).commutes a
  let r₁ : Lift O (toMat (r.psib v i)) (ResidueField O) :=
    { hom := toMat (r.psib v i)
      cont := fun a b N => hlc.comp fun x => Ideal.Quotient.mk _ (x : ResidueField O)
      red := fun g a b => hres _ }
  obtain ⟨R, _, _, _, p, -, hR⟩ := univ_cond O (F.Gv v) Unit _ R₀ u _ P hu hP
    ⟨ResidueField O, inferInstance, inferInstance, inferInstance, r₁, trivial, fun g => psib_th r v i g⟩
  refine ⟨R, inferInstance, inferInstance, inferInstance, ofMat (u.map p).hom,
    ⟨(u.map p).cont () (), fun g => (u.map p).red g () (), ((hR R).1 (AlgHom.id O R)).2⟩, fun R' _ _ _ ψ' h' => ?_⟩
  let s : Lift O (toMat (r.psib v i)) R' :=
    { hom := toMat ψ'
      cont := fun a b => h'.cont
      red := fun g a b => h'.red g }
  obtain ⟨f, hf, huniq⟩ := (hR R').2 s ⟨trivial, h'.mu⟩
  refine ⟨f, ?_, fun f' hf' => huniq f' ?_⟩
  · ext g
    exact congrArg (fun t : Lift O (toMat (r.psib v i)) R' => t.hom g () ()) hf
  · ext g a b
    exact congrArg (fun t : F.Gv v →* R'ˣ => ((t g : R'ˣ) : R')) hf'
