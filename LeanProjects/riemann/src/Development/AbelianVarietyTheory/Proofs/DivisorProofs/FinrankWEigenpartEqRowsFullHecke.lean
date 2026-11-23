import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Formalism.LocalToGlobal.IndefiniteReal.CutTuples2
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SignAtBasePlaceEqEmbedding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMapMemMult
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodPartFullEqKilled
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryMatchingLatticesMatchesSphericalOpsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLabelThetaLiftSpaceIffDualStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelOperatorsAtPrimeOffLevelDatumStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSphericalOperatorsRowsNormalEigenspacesStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalOperatorsFormsOnRankSpaceNormalStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.DimFull

open GlobalTheory.CuspMult GlobalTheory.PartDims

theorem dualLab_twice (d : List ℤ) : dualLab (dualLab d) = d := by
  simp [dualLab, List.map_reverse, Function.comp_def]

variable {D : D7}

section Adj

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

theorem star_eq_of_normal {ok : Pl D.host.E → Prop} {h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ H}
    (hN : GlobalTheory.Hk3.NormalFam ok h) {P : Pl D.host.E} (hP : ok P) (d : List ℤ) {x : H} (hx : x ≠ 0) {a b : ℂ}
    (h1 : h P (Finsupp.single d 1) x = a • x) (h2 : h P (Finsupp.single (dualLab d) 1) x = b • x) : star a = b := by
  have hadj := hN.2 P hP (Finsupp.single d 1)
  have hc : GlobalTheory.Hk3.dualC (Finsupp.mapRange star (star_zero ℂ) (Finsupp.single d (1 : ℂ))) = Finsupp.single (dualLab d) 1 := by
    simp [GlobalTheory.Hk3.dualC, Finsupp.mapRange_single, Finsupp.mapDomain_single]
  rw [hc] at hadj
  have e := LinearMap.adjoint_inner_right (h P (Finsupp.single d 1)) x x
  rw [hadj, h1, h2, inner_smul_left, inner_smul_right] at e
  have h0 : (inner ℂ x x : ℂ) ≠ 0 := inner_self_ne_zero.2 hx
  exact (mul_right_cancel₀ h0 e).symm

end Adj

theorem evC_single (V : HSp D) (P : Pl D.host.E) (a : List ℤ → ℂ) {d : List ℤ} (hd : IsLab V P d) :
    GlobalTheory.Hk3.evC V P a (Finsupp.single d 1) = a d := by
  classical
  unfold GlobalTheory.Hk3.evC
  rw [Finsupp.sum_single_index (by simp)]
  simp [hd]

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}

theorem liftsY' (h : Core R F) : LiftsExist (Yc D 0) (R.βY 0) (R.dat0 R.triv) := by
  obtain ⟨c, hc⟩ := h.lev.βY 0 (lt_of_lt_of_le two_pos D.R.two_le_m)
  exact GlobalTheory.T.finite_group_lifts_to_parahoric_level _ _ _ _ _ hc rfl (GlobalTheory.T.typePlaces_not_pairwise_conjugate R.C.P R.Pg h.lev.Pg)

theorem liftsW' (h : Core R F) (i : Fin D.R.m) : LiftsExist (Wc D i) (R.βW i) (R.datWp i R.triv) := by
  obtain ⟨c, hc⟩ := h.lev.βW i
  exact GlobalTheory.T.finite_group_lifts_to_parahoric_level _ _ _ _ _ hc rfl (GlobalTheory.T.typePlaces_not_pairwise_conjugate R.C.P R.Pg h.lev.Pg)

theorem lab_dual (h : Core R F) (i : Fin D.R.m) {Q : Pl D.host.E} (hQ : Good R A.μ0 Q) {d : List ℤ}
    (hd : IsLab (Yc D 0) Q d) : IsLab (Yc D 0) Q (dualLab d) ∧ IsLab (Wc D i) Q d ∧ IsLab (Wc D i) Q (dualLab d) := by
  have l1 := GlobalTheory.T.isLabel_thetaLiftSpace_iff_dual (s := 0) R F h i Q d hQ
  have l2 := GlobalTheory.T.isLabel_thetaLiftSpace_iff_dual (s := 0) R F h i Q (dualLab d) hQ
  have w := l1.2.2 hd
  have y := l1.1.1 w
  exact ⟨y, w, l2.2.2 y⟩

theorem rel_of_E (h : Core R F) (hS : SchurAll R) {SF} (hSF : IsSF R SF) (i : Fin D.R.m) {c : Pl D.host.E → List ℤ → ℂ} {x : R.HE.H}
    (hx : x ∈ EEc R SF c) (h0 : x ≠ 0) {Q : Pl D.host.E} (hQ : Good R A.μ0 Q) {d : List ℤ} (hd : IsLab (Yc D 0) Q d) :
    star (c Q (dualLab d)) = c Q d := by
  obtain ⟨o, -, hN, -, hev, -⟩ := GlobalTheory.T.exists_sphericalOperators_rows_normal_eigenspaces R F h hS SF hSF
  have hdd := (lab_dual h i hQ hd).1
  have h1 := hev c Q hQ (Finsupp.single d 1) x hx
  have h2 := hev c Q hQ (Finsupp.single (dualLab d) 1) x hx
  rw [evC_single _ _ _ hd] at h1
  rw [evC_single _ _ _ hdd, dualLab_twice] at h2
  exact star_eq_of_normal hN hQ d h0 h1 h2

theorem unitary_relation_labels_of_W_eigenvector (h : Core R F) (hS : SchurAll R) (hI : ∀ χ ∈ A.X, IsAbsIrrChar χ) {SF} (hSF : IsSF R SF) (i : Fin D.R.m)
    {c : Pl D.host.E → List ℤ → ℂ} {x : (R.HW i (sg0 D A)).H}
    (hx : x ∈ Wcc R SF i c) (h0 : x ≠ 0) {Q : Pl D.host.E} (hQ : Good R A.μ0 Q) {d : List ℤ} (hd : IsLab (Yc D 0) Q d) :
    star (c Q (dualLab d)) = c Q d := by
  obtain ⟨o, -, hN, -, -, -, hev, -⟩ := GlobalTheory.T.sphericalOperators_forms_on_rank_space_normal R F h hS hI SF hSF i
  obtain ⟨-, hw, hwd⟩ := lab_dual h i hQ hd
  have h1 := hev c Q hQ (Finsupp.single (dualLab d) 1) x hx
  have h2 := hev c Q hQ (Finsupp.single d 1) x hx
  rw [evC_single _ _ _ hwd] at h1
  rw [evC_single _ _ _ hw] at h2
  refine star_eq_of_normal hN hQ (dualLab d) h0 h1 ?_
  rw [dualLab_twice]
  exact h2

theorem good_Y (h : Core R F) {Q : Pl D.host.E} (hQ : Good R A.μ0 Q) (c : ℕ) :
    (((((D.host.g 0 * D.host.g 1) ^ c : ℕ)) : 𝓞 D.host.E)) ∉ Q.asIdeal := by
  obtain ⟨-, hg, -⟩ := GlobalTheory.T.theta_lift_levels_good_primes_properties R F h.lev
  intro hc
  rw [Nat.cast_pow] at hc
  exact (hg _ _ hQ).1 (Q.isPrime.mem_of_pow_mem c hc)

theorem one_pow_not_mem_height_one_asIdeal {Q : Pl D.host.E} (c : ℕ) : ((((1 ^ c : ℕ)) : 𝓞 D.host.E)) ∉ Q.asIdeal := by
  intro hc
  rw [one_pow, Nat.cast_one] at hc
  exact Q.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 hc)

theorem hecke_Y (h : Core R F) {SF} (hSF : IsSF R SF) {Q : Pl D.host.E} (hQ : Good R A.μ0 Q) (d : List ℤ) (B : Finset (GA D (Yc D 0))) :
    Hecke₂ (Yc D 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) SF Q d B ↔
      GlobalTheory.Hk3.SphOp (Yc D 0) Q d B := by
  obtain ⟨c, hc⟩ := h.lev.βY 0 (lt_of_lt_of_le two_pos D.R.two_le_m)
  obtain ⟨-, -, hoff, -⟩ := GlobalTheory.T.theta_lift_levels_good_primes_properties R F h.lev
  rw [(GlobalTheory.T.level_operators_at_prime_off_level_datum (Yc D 0) (R.βY 0) (R.ΛY 0) _ (R.dat0 R.triv) hc Q (good_Y h hQ c)
    (fun PP hPP => hQ PP (Or.inl (hPP.resolve_right (Finset.notMem_empty _))))).2.1 SF d B]
  exact ⟨fun x => x.2, fun x => ⟨(hoff SF hSF Q).2 hQ, x⟩⟩

theorem isHeckeOpFull_iff_sphOp (h : Core R F) {SF} (hSF : IsSF R SF) (i : Fin D.R.m) {Q : Pl D.host.E} (hQ : Good R A.μ0 Q) (d : List ℤ)
    (B : Finset (GA D (Wc D i))) :
    Hecke₂ (Wc D i) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) SF Q d B ↔
      GlobalTheory.Hk3.SphOp (Wc D i) Q d B := by
  obtain ⟨c, hc⟩ := h.lev.βW i
  obtain ⟨-, -, hoff, -⟩ := GlobalTheory.T.theta_lift_levels_good_primes_properties R F h.lev
  rw [(GlobalTheory.T.level_operators_at_prime_off_level_datum (Wc D i) (R.βW i) (R.ΛW i) _ (R.datWp i R.triv) hc Q (one_pow_not_mem_height_one_asIdeal c)
    (fun PP hPP => hQ PP (Or.inl (hPP.resolve_right (Finset.notMem_empty _))))).2.1 SF d B]
  exact ⟨fun x => x.2, fun x => ⟨(hoff SF hSF Q).2 hQ, x⟩⟩

theorem good_of_hecke {V : HSp D} (h : Core R F) {SF} (hSF : IsSF R SF) {J : Set (GA D V)} {χ : GA D V → ℂ} {Q : Pl D.host.E} {d : List ℤ}
    {B : Finset (GA D V)} (hB : Hecke₂ V J χ SF Q d B) : Good R A.μ0 Q := by
  obtain ⟨-, -, hoff, -⟩ := GlobalTheory.T.theta_lift_levels_good_primes_properties R F h.lev
  obtain ⟨e, f, ϖ, α, hO, -⟩ := hB
  exact (hoff SF hSF Q).1 hO

theorem hecke_trans (h : Core R F) {SF} (hSF : IsSF R SF) (i : Fin D.R.m)
    {j : Matrix (Fin (Wc D i).rank) (Fin (Yc D 0).rank) (Lev.EAf D)} {Φ : GfC (Yc D 0) ≃ₜ* GfC (Wc D i)}
    (hΦ : IsFinIso (Yc D 0) (Wc D i) (R.βY 0) (R.βW i) R.Pg j Φ) (Q : Pl D.host.E) (d : List ℤ) (B : Finset (GfC (Yc D 0))) :
    Hecke₂ (Yc D 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) SF Q d
        (B.map ⟨Subtype.val, Subtype.val_injective⟩) ↔
      Hecke₂ (Wc D i) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) SF Q d
        ((B.map Φ.toEquiv.toEmbedding).map ⟨Subtype.val, Subtype.val_injective⟩) := by
  by_cases hQ : Good R A.μ0 Q
  · obtain ⟨c, hc⟩ := h.lev.βY 0 (lt_of_lt_of_le two_pos D.R.two_le_m)
    obtain ⟨c', hc'⟩ := h.lev.βW i
    rw [hecke_Y h hSF hQ, isHeckeOpFull_iff_sphOp h hSF i hQ]
    exact GlobalTheory.T.isometry_matching_lattices_matches_spherical_ops (Yc D 0) (Wc D i) (R.βY 0) (R.βW i) R.Pg j Φ (R.ΛY 0) (R.ΛW i) _ _ hc hc' hΦ Q (good_Y h hQ c) (one_pow_not_mem_height_one_asIdeal c') d B
  · exact ⟨fun e => absurd (good_of_hecke h hSF e) hQ, fun e => absurd (good_of_hecke h hSF e) hQ⟩

section Alg

variable {H H' X : Type} [Group H] [Group H'] [AddCommGroup X] [Module ℂ X]

theorem alg_comp (ρ : Representation ℂ H' X) (Φ : H ≃* H') (B : Finset H) (z : ℂ) (v : X) :
    Representation.asAlgebraHom (ρ.comp Φ.toMonoidHom : Representation ℂ H X)
        (∑ γ ∈ B, MonoidAlgebra.single γ 1 - MonoidAlgebra.single 1 z) v =
      ρ.asAlgebraHom (∑ γ ∈ B.map Φ.toEquiv.toEmbedding, MonoidAlgebra.single γ 1 - MonoidAlgebra.single 1 z) v := by
  simp [map_sub, map_sum, Representation.asAlgebraHom_single, Finset.sum_map, LinearMap.sum_apply]

end Alg

theorem killed_le_left {H X : Type} [Group H] [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ H X)
    (I I' : Set (MonoidAlgebra ℂ H)) : killed ρ (I ∪ I') ≤ killed ρ I :=
  fun _ hv => ((GlobalTheory.CuspMult.CutFull.mem_killed_union ρ I I' _).1 hv).1

theorem killed_union_comp {H H' X ι κ : Type} [Group H] [Group H'] [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ H' X) (Φ : H ≃* H')
    {E : Set (MonoidAlgebra ℂ H)} {E' : Set (MonoidAlgebra ℂ H')}
    (hE : killed (ρ.comp Φ.toMonoidHom : Representation ℂ H X) E = killed ρ E')
    (I : ι → κ → Finset H → Prop) (I' : ι → κ → Finset H' → Prop) (a : ι → κ → ℂ)
    (hI : ∀ Q d B, I Q d B ↔ I' Q d (B.map Φ.toEquiv.toEmbedding)) :
    killed (ρ.comp Φ.toMonoidHom : Representation ℂ H X)
        (E ∪ {x | ∃ Q d B, I Q d B ∧ x = ∑ γ ∈ B, MonoidAlgebra.single γ 1 - MonoidAlgebra.single 1 (a Q d)}) =
      killed ρ (E' ∪ {x | ∃ Q d B, I' Q d B ∧ x = ∑ γ ∈ B, MonoidAlgebra.single γ 1 - MonoidAlgebra.single 1 (a Q d)}) := by
  ext v
  rw [GlobalTheory.CuspMult.CutFull.mem_killed_union, GlobalTheory.CuspMult.CutFull.mem_killed_union, hE]
  refine and_congr_right fun _ => ?_
  rw [mem_killed, mem_killed]
  constructor
  · rintro hk x ⟨Q, d, B', hB', rfl⟩
    have hm : (B'.map Φ.symm.toEquiv.toEmbedding).map Φ.toEquiv.toEmbedding = B' := by
      ext y
      simp [Finset.mem_map]
    have := hk _ ⟨Q, d, B'.map Φ.symm.toEquiv.toEmbedding, (hI _ _ _).2 (by rw [hm]; exact hB'), rfl⟩
    rw [alg_comp, hm] at this
    exact this
  · rintro hk x ⟨Q, d, B, hB, rfl⟩
    rw [alg_comp]
    exact hk _ ⟨Q, d, _, (hI _ _ _).1 hB, rfl⟩

theorem count (h : Core R F) (hD : CuspDecomp D) (hM : MultEq R) (i : Fin D.R.m)
    (M₀ : DSModel (Yc D 0) (parA (Ptw D) 0)) (P : LevelP R.Pg D.R.r ℂ) {SF} (hSF : IsSF R SF) (a : Pl D.host.E → List ℤ → ℂ)
    (f1 : FiniteDimensional ℂ (goodPart R.θ M₀ (levS _ (R.βY 0) (R.dat0 P)) (levChi _ (R.βY 0) (R.dat0 P)) R.e0 ⊓
      partFull R.θ M₀ (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) SF a : Submodule ℂ (MMap M₀)))
    (f2 : FiniteDimensional ℂ (R.Wat i (sg0 D A) P ⊓
      partFull R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) SF a :
        Submodule ℂ (MMap (R.MW i (sg0 D A))))) :
    Module.finrank ℂ (goodPart R.θ M₀ (levS _ (R.βY 0) (R.dat0 P)) (levChi _ (R.βY 0) (R.dat0 P)) R.e0 ⊓
      partFull R.θ M₀ (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) SF a : Submodule ℂ (MMap M₀)) =
    Module.finrank ℂ (R.Wat i (sg0 D A) P ⊓
      partFull R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) SF a :
        Submodule ℂ (MMap (R.MW i (sg0 D A)))) := by
  obtain ⟨c, hc⟩ := h.lev.βY 0 (lt_of_lt_of_le two_pos D.R.two_le_m)
  obtain ⟨c', hc'⟩ := h.lev.βW i
  have hrk : (Yc D 0).rank = (Wc D i).rank := rank_zeroth_component_eq.trans (rank_weight_component_eq i).symm
  obtain ⟨j, Φ, hΦ⟩ := GlobalTheory.T.exists_finiteAdelic_isometry_matching_frames (Yc D 0) (Wc D i) (R.βY 0) (R.ΛY 0) _ (R.βW i) (R.ΛW i) _ R.Pg hrk hc hc'
    (GlobalTheory.T.typePlaces_not_pairwise_conjugate R.C.P R.Pg h.lev.Pg)
  have e1 : (goodPart R.θ M₀ (levS _ (R.βY 0) (R.dat0 P)) (levChi _ (R.βY 0) (R.dat0 P)) R.e0 ⊓
      partFull R.θ M₀ (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) SF a : Submodule ℂ (MMap M₀)) = _ :=
    GlobalTheory.CuspMult.CutFull.good_partFull_eq_killed R.θ M₀ (R.βY 0) (R.dat0 R.triv) R.eG
    (RealDat.eC (A := A) D.what₂.embLL) P SF a rfl rfl (liftsY' h)
  have e2 : (R.Wat i (sg0 D A) P ⊓
      partFull R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) SF a :
        Submodule ℂ (MMap (R.MW i (sg0 D A)))) = _ :=
    GlobalTheory.CuspMult.CutFull.good_partFull_eq_killed R.θ (R.MW i (sg0 D A)) (R.βW i) (R.datWp i R.triv) R.eG
    (RealDat.eC (A := A) (sg0 D A)) P SF a rfl rfl (liftsW' h i)
  have e3 : RealDat.eC (A := A) (sg0 D A) = RealDat.eC (A := A) D.what₂.embLL := by rw [sign_at_base_place_eq_embedding R]
  have hl := GlobalTheory.T.isometry_matches_parahoric_levels (Yc D 0) (Wc D i) (R.βY 0) (R.βW i) D.R.r D.R.t (r_le_Y 0) (r_le_rank_Wc i) R.Pg R.chi
    (fun _ _ => 1) j Φ hΦ
  have e4 : killed ((finRep (R.MW i (sg0 D A))).comp Φ.toMulEquiv.toMonoidHom : Representation ℂ (GfC (Yc D 0)) _)
        (eqSet (Yc D 0) (R.βY 0) (R.dat0 R.triv) R.eG (RealDat.eC (A := A) D.what₂.embLL) P (∅ : Set Empty) Empty.elim Empty.elim Empty.elim) =
      killed (finRep (R.MW i (sg0 D A))) (eqSet (Wc D i) (R.βW i) (R.datWp i R.triv) R.eG
        (RealDat.eC (A := A) D.what₂.embLL) P (∅ : Set Empty) Empty.elim Empty.elim Empty.elim) :=
    GlobalTheory.T.levelTypeHecke_killed_correspond_matching_iso (Yc D 0) (Wc D i) (R.βY 0) (R.βW i) D.R.r D.R.t (r_le_Y 0) (r_le_rank_Wc i) R.Pg R.chi (fun _ _ => 1) Φ R.eG _ P
      (∅ : Set Empty) Empty.elim Empty.elim Empty.elim _ _ hrk (fun κ => (hl κ).1) (fun κ => (hl κ).2) (fun P0 => P0.elim)
  have e5 := killed_union_comp (finRep (R.MW i (sg0 D A))) Φ.toMulEquiv e4
    (fun Q d B => Hecke₂ (Yc D 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) SF Q d
        (B.map ⟨Subtype.val, Subtype.val_injective⟩))
    (fun Q d B => Hecke₂ (Wc D i) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) SF Q d
        (B.map ⟨Subtype.val, Subtype.val_injective⟩)) a (hecke_trans h hSF i hΦ)
  rw [e1] at f1 ⊢
  rw [e2, e3] at f2 ⊢
  erw [← e5] at f2 ⊢
  refine GlobalTheory.T.finrank_killed_eq_of_equal_multiplicities _ _ _ (finRep M₀) _ _ _ _ (hD R.θ h.models.inf _ _ M₀)
    (GlobalTheory.T.irreducibleAdmissibleDecomposable_comp_equiv _ _ _ _ _ Φ (hD R.θ h.models.inf _ _ (R.MW i (sg0 D A)))) ?_
    (fun x hx => isOpen_stab rfl rfl (killed_le_left _ _ _ hx)) (fun x hx => isOpen_stab rfl rfl (killed_le_left _ _ _ hx)) f1 f2
  intro W _ _ σ h1 h2 h3
  rw [homInto_comp]
  refine hM i M₀ j Φ hΦ W σ h1 h2 (isGoodRep_of_killed (P := P) (ok := (∅ : Set Empty)) (pl := Empty.elim) (q := Empty.elim)
    (Sg := Empty.elim) rfl rfl (liftsY' h) fun e => h3 ?_)
  exact le_bot_iff.1 (e ▸ killed_le_left _ _ _)

theorem star_levChi' (Pp : Subgroup G) (ψ : Pp →* D.what₂.LLˣ) {κ : GA D (Yc D 0)}
    (hκ : κ ∈ levS _ (R.βY 0) (R.dat0 (levPOf R.eG D.what₂.embLL Pp ψ))) :
    levChi _ (R.βY 0) (R.dat0 (levPOf R.eG D.what₂.embLL Pp ψ⁻¹)) κ =
      star (levChi _ (R.βY 0) (R.dat0 (levPOf R.eG D.what₂.embLL Pp ψ)) κ) := by
  have hm : rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) κ) ∈ (levPOf R.eG D.what₂.embLL Pp ψ).H := hκ.2.2
  have h1 := levChi_withP (β := R.βY 0) (L := R.dat0 R.triv) rfl rfl (levPOf R.eG D.what₂.embLL Pp ψ⁻¹) κ
  have h2 := levChi_withP (β := R.βY 0) (L := R.dat0 R.triv) rfl rfl (levPOf R.eG D.what₂.embLL Pp ψ) κ
  replace h2 := h2.trans (congrArg Units.val (extendOne_of_mem (P := (levPOf R.eG D.what₂.embLL Pp ψ).H) (levPOf R.eG D.what₂.embLL Pp ψ).chi hm))
  replace h1 := h1.trans (congrArg Units.val (extendOne_of_mem (P := (levPOf R.eG D.what₂.embLL Pp ψ⁻¹).H) (levPOf R.eG D.what₂.embLL Pp ψ⁻¹).chi hm))
  refine h1.trans (Eq.trans ?_ (congrArg star h2).symm)
  have h3 : (levPOf R.eG D.what₂.embLL Pp ψ⁻¹).chi ⟨_, hm⟩ = ((levPOf R.eG D.what₂.embLL Pp ψ).chi ⟨_, hm⟩)⁻¹ := by
    exact map_inv (Units.map D.what₂.embLL.toMonoidHom) _
  have h4 : IsOfFinOrder ((levPOf R.eG D.what₂.embLL Pp ψ).chi ⟨_, hm⟩) := by
    have : Finite (G0 R.Pg D.R.r) := Finite.of_equiv _ R.eG.toEquiv
    exact MonoidHom.isOfFinOrder _ (isOfFinOrder_of_finite _)
  have h5 : ‖(((levPOf R.eG D.what₂.embLL Pp ψ).chi ⟨_, hm⟩ : ℂˣ) : ℂ)‖ = 1 := ((Units.coeHom ℂ).isOfFinOrder h4).norm_eq_one
  rw [h3, Units.val_inv_eq_inv_val, Complex.inv_eq_conj h5]
  rfl

theorem finrank_rel {s : ℕ} (hs : A.fam.Ok s) (hC : Core R F) (hX : GoodStable A.X) (hD : CuspDecomp D) (hM : MultEq R) {SF} (hSF : IsSF R SF)
    (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (i : Fin D.R.m) (c : Pl D.host.E → List ℤ → ℂ)
    (hrel : ∀ Q, Good R A.μ0 Q → ∀ d, IsLab (Yc D 0) Q d → star (c Q (dualLab d)) = c Q d) :
    Module.finrank ℂ (Wcc R SF i c ⊓ (R.Wat i (sg0 D A) (levPOf R.eG (sg0 D A) P ψ⁻¹)).comap (R.HW i _).e : Submodule ℂ _) =
      Module.finrank ℂ (EEc R SF c ⊓ (R.EEat (levPOf R.eG D.what₂.embLL P ψ)).comap R.HE.e : Submodule ℂ _) := by
  have hl : levPOf R.eG (sg0 D A) P ψ⁻¹ = levPOf R.eG D.what₂.embLL P ψ⁻¹ := by rw [sign_at_base_place_eq_embedding R]
  rw [hl]
  have hW : R.Wat i (sg0 D A) (levPOf R.eG D.what₂.embLL P ψ⁻¹) ≤ R.Wat i (sg0 D A) R.triv :=
    goodPart_le_flag (L := R.datWp i R.triv) R.θ _ rfl rfl _ _
  have hE : R.EEat (levPOf R.eG D.what₂.embLL P ψ) ≤ R.EEat R.triv := goodPart_le_flag (L := R.dat0 R.triv) R.θ _ rfl rfl _ _
  have eW : (Wcc R SF i c ⊓ (R.Wat i (sg0 D A) (levPOf R.eG D.what₂.embLL P ψ⁻¹)).comap (R.HW i _).e : Submodule ℂ _) =
      (R.Wat i (sg0 D A) (levPOf R.eG D.what₂.embLL P ψ⁻¹) ⊓
        partFull R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) SF c).comap (R.HW i _).e := by
    ext x
    exact ⟨fun hx => ⟨hx.2, hx.1.2⟩, fun hx => ⟨⟨hW hx.1, hx.2⟩, hx.1⟩⟩
  have eE : (EEc R SF c ⊓ (R.EEat (levPOf R.eG D.what₂.embLL P ψ)).comap R.HE.e : Submodule ℂ _) =
      (R.EEat (levPOf R.eG D.what₂.embLL P ψ) ⊓
        partFull R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) SF
          (fun Q d => c Q (dualLab d))).comap R.HE.e := by
    ext x
    exact ⟨fun hx => ⟨hx.2, hx.1⟩, fun hx => ⟨hx.2, hx.1⟩⟩
  rw [eW, eE]
  obtain ⟨M₀, cc, hcc⟩ := exists_conjModel (S' := parA (Ptw D) 0)
    (fun τ => by rw [Nat.zero_min]; exact (dualPar_dualPar _).symm) (R.MY 0)
  have hχ0 : ∀ k ∈ levS _ (R.βY 0) (R.dat0 R.triv), levChi _ (R.βY 0) (R.dat0 R.triv) k = star (levChi _ (R.βY 0) (R.dat0 R.triv) k) := by
    intro k hk
    have h1 : levChi _ (R.βY 0) (R.dat0 R.triv) k = 1 := (mem_levi_flag_of_mem_parabolic (L := R.dat0 R.triv) rfl rfl R.triv hk).2.2
    rw [h1, star_one]
  have hr := GlobalTheory.ConjFull.conj_rank_full R.θ (R.MY 0) M₀ cc hcc (levS _ (R.βY 0) (R.dat0 (levPOf R.eG D.what₂.embLL P ψ)))
    (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 (levPOf R.eG D.what₂.embLL P ψ)))
    (levChi _ (R.βY 0) (R.dat0 (levPOf R.eG D.what₂.embLL P ψ⁻¹))) (levChi _ (R.βY 0) (R.dat0 R.triv)) R.e0 R.e0 SF
    (fun Q d => c Q (dualLab d)) (fun k hk => star_levChi' P ψ hk) hχ0
    (gaL_star (L := R.dat0 R.triv) R.eG _ rfl rfl (GlobalTheory.T.star_idemOf_coeff_eq_self D.what₂.embLL A.X hs.irr hX))
  have hU : partFull R.θ M₀ (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) SF
        (fun Q d => star (c Q (dualLab d))) =
      partFull R.θ M₀ (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) SF c := by
    have key : ∀ Q d B, Hecke₂ (Yc D 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) SF Q d B →
        star (c Q (dualLab d)) = c Q d := fun Q d B hB =>
      hrel Q (good_of_hecke hC hSF hB) d ⟨B, (hecke_Y hC hSF (good_of_hecke hC hSF hB) d B).1 hB⟩
    ext U
    rw [GlobalTheory.CuspMult.CutFull.mem_partFull_iff, GlobalTheory.CuspMult.CutFull.mem_partFull_iff]
    refine and_congr_right fun _ => ⟨fun hh Q d B hB v x => ?_, fun hh Q d B hB v x => ?_⟩
    · rw [← key Q d B hB]
      exact hh Q d B hB v x
    · rw [key Q d B hB]
      exact hh Q d B hB v x
  rw [hU] at hr
  have hr' : Module.rank ℂ (R.EEat (levPOf R.eG D.what₂.embLL P ψ) ⊓
        partFull R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) SF
          (fun Q d => c Q (dualLab d)) : Submodule ℂ (MMap (R.MY 0))) =
      Module.rank ℂ (goodPart R.θ M₀ (levS _ (R.βY 0) (R.dat0 (levPOf R.eG D.what₂.embLL P ψ⁻¹)))
        (levChi _ (R.βY 0) (R.dat0 (levPOf R.eG D.what₂.embLL P ψ⁻¹))) R.e0 ⊓
        partFull R.θ M₀ (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) SF c : Submodule ℂ (MMap M₀)) := hr
  have fE := (finrank_comap hC.models.HE (U := R.EEat (levPOf R.eG D.what₂.embLL P ψ) ⊓
    partFull R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) SF
      (fun Q d => c Q (dualLab d))) (inf_le_left.trans hE))
  have fW := (finrank_comap (hC.models.HW i (sg0 D A)) (U := R.Wat i (sg0 D A) (levPOf R.eG D.what₂.embLL P ψ⁻¹) ⊓
    partFull R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) SF c)
    (inf_le_left.trans (hW.trans inf_le_left)))
  rw [fW.1, fE.1]
  have f1 := Module.rank_lt_aleph0_iff.1 (lt_of_eq_of_lt hr'.symm (Module.rank_lt_aleph0_iff.2 fE.2))
  rw [← count hC hD hM i M₀ _ hSF c f1 fW.2]
  exact congrArg Cardinal.toNat hr'.symm

end GlobalTheory.DimFull

open GlobalTheory.DimFull in

theorem GlobalTheory.DimFull.dim_parts_full : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) {s : ℕ}, A.fam.Ok s → Core R F → SchurAll R → GoodStable A.X → GlobalTheory.CuspMult.CuspDecomp D → GlobalTheory.CuspMult.MultEq R → ∀ SF, IsSF R SF → ∀ (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) i c, Module.finrank ℂ (Wcc R SF i c ⊓ (R.Wat i (sg0 D A) (levPOf R.eG (sg0 D A) P ψ⁻¹)).comap (R.HW i _).e : Submodule ℂ _) = Module.finrank ℂ (EEc R SF c ⊓ (R.EEat (levPOf R.eG D.what₂.embLL P ψ)).comap R.HE.e : Submodule ℂ _) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F s hs hC hS hX hD hM SF hSF P ψ i c
  by_cases hrel : ∀ Q, Good R A.μ0 Q → ∀ d, IsLab (Yc D 0) Q d → star (c Q (dualLab d)) = c Q d
  · exact finrank_rel hs hC hX hD hM hSF P ψ i c hrel
  · have h1 : Wcc R SF i c = ⊥ := by
      by_contra hne
      obtain ⟨x, hx, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
      exact hrel fun Q hQ d hd => unitary_relation_labels_of_W_eigenvector hC hS hs.irr hSF i hx h0 hQ hd
    have h2 : EEc R SF c = ⊥ := by
      by_contra hne
      obtain ⟨x, hx, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
      exact hrel fun Q hQ d hd => rel_of_E hC hS hSF i hx h0 hQ hd
    rw [h1, h2, bot_inf_eq, bot_inf_eq, finrank_bot, finrank_bot]

end
