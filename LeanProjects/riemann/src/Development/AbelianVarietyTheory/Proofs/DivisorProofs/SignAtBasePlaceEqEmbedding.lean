import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.IndefiniteReal.CutTuples2
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitDetOfSplitDetermines
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemNotMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteGroupLiftsToParahoricLevelStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesModelOfDualParameterStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleAdmissibleDecomposableCompEquivStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemOfCoeffRealStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamilyPolynomialDegreeLeRankStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualPolynomialCoefficientsEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodFormsEqKilledByGroupAlgebraStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelTypeHeckeKilledCorrespondMatchingIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryMatchesParahoricLevelsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePlacesNotPairwiseConjugateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateModelsMultiplicityEqualStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankKilledEqOfEqualMultiplicitiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeEigenvalueAtBaseFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCompatFiniteIsometryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicIsometryMatchingFramesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyMulRight

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult

namespace GlobalTheory.PartDims

section Lin

theorem finrank_twSub (s : Bool) {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (V : Submodule ℂ E) :
    Module.finrank ℂ (Tw.sub s V) = Module.finrank ℂ V := by
  unfold Module.finrank
  congr 1
  refine rank_eq_of_equiv_equiv (cj s)
    { toFun := fun x => ⟨Tw.out x.1, x.2⟩
      invFun := fun x => ⟨Tw.mk s x.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl } ?_ (fun _ _ => rfl)
  exact Function.Involutive.bijective (cj_cj s)

theorem finrank_comap {X : Type} [AddCommGroup X] [Module ℂ X] {M : HMod X} {V U : Submodule ℂ X} {ip : X → X → ℂ}
    (h : M.Is V ip) (hU : U ≤ V) : Module.finrank ℂ (U.comap M.e) = Module.finrank ℂ U ∧ FiniteDimensional ℂ U := by
  have e : U.comap M.e ≃ₗ[ℂ] U :=
    (Submodule.equivMapOfInjective M.e h.1 (U.comap M.e)).trans
      (LinearEquiv.ofEq _ _ (Submodule.map_comap_eq_self (h.2.1.symm ▸ hU)))
  exact ⟨e.finrank_eq, e.finiteDimensional⟩

theorem homInto_comp {H H' S X : Type} [Group H] [Group H'] [AddCommGroup S] [Module ℂ S] [AddCommGroup X] [Module ℂ X]
    (σ : Representation ℂ H S) (ρ : Representation ℂ H' X) (C : Submodule ℂ X) (Φ : H ≃* H') :
    homInto σ (ρ.comp Φ.toMonoidHom : Representation ℂ H X) C =
      homInto (σ.comp Φ.symm.toMonoidHom : Representation ℂ H' S) ρ C := by
  ext f
  refine and_congr_right fun _ => ⟨fun h g s => ?_, fun h g s => ?_⟩
  · have := h (Φ.symm g) s
    simpa using this
  · have := h (Φ g) s
    simpa using this

end Lin

variable {D : D7}

section Level

variable {V : HSp D} {β : GL (Fin V.rank) (EAf D)} {L : LevDat D.host.E ℂ V.rank}

theorem levChi_flag (hs : L.s = 0) (hQ : L.Q = ∅) (κ : GA D V) : levChi V β (flagL L) κ = 1 := by
  have h2 : ext1 (flagL L).P.H (flagL L).P.chi (rTup β (flagL L) (finE V κ)) = 1 := subgroupCharExtension_one_apply _ _
  unfold levChi levFn
  rw [h2]
  simp [flagL, withP, hs, hQ]

theorem levChi_withP (hs : L.s = 0) (hQ : L.Q = ∅) (P : LevelP L.Pg L.r ℂ) (κ : GA D V) :
    levChi V β (withP L P) κ = ((ext1 P.H P.chi (rTup β L (finE V κ)) : ℂˣ) : ℂ) := by
  have h := levChi_flag (β := β) hs hQ κ
  unfold levChi at h ⊢
  rw [levFn_withP, Units.val_mul, h, mul_one]

theorem mem_levi_flag_of_mem_parabolic (hs : L.s = 0) (hQ : L.Q = ∅) (P : LevelP L.Pg L.r ℂ) {κ : GA D V} (hκ : κ ∈ levG V β (flag1L L)) :
    κ ∈ levG V β (withP L P) ∧ levChi V β (withP L P) κ = 1 ∧ levChi V β (flag1L L) κ = 1 := by
  have h1 : rTup β L (finE V κ) = 1 := Subgroup.mem_bot.1 hκ.2.2
  refine ⟨⟨hκ.1, hκ.2.1, ?_⟩, ?_, ?_⟩
  · show rTup β L (finE V κ) ∈ P.H
    rw [h1]; exact P.H.one_mem
  · rw [levChi_withP hs hQ, h1, blockDiagonalExtendByOnePrimeField_one]; rfl
  · have h := levChi_flag (β := β) hs hQ κ
    unfold levChi at h ⊢
    rw [levFn_flag1, h]

theorem mult_le {S : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S)
    {J J' : Set (GA D V)} {χ χ' : GA D V → ℂ} (h : ∀ k ∈ J', k ∈ J ∧ χ k = χ' k) : Mult θ M J χ ≤ Mult θ M J' χ' := by
  refine Submodule.span_mono fun T hT => ⟨hT.aut, hT.cusp, fun v k hk g => ?_, hT.equiv, hT.cont⟩
  rw [← (h k hk).2]
  exact hT.lev v k (h k hk).1 g

theorem goodPart_le_flag {S : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (M : DSModel V S) (hs : L.s = 0) (hQ : L.Q = ∅) (P : LevelP L.Pg L.r ℂ) (e : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) :
    goodPart θ M (levS V β (withP L P)) (levChi V β (withP L P)) e ≤
      goodPart θ M (levS V β (flag1L L)) (levChi V β (flag1L L)) e :=
  inf_le_inf_right _ (mult_le θ M fun k hk => by
    obtain ⟨h1, h2, h3⟩ := mem_levi_flag_of_mem_parabolic hs hQ P hk
    exact ⟨h1, h2.trans h3.symm⟩)

variable {G : Type} [Group G] [Fintype G] (eG : G ≃* G0 L.Pg L.r) (c : G → ℂ)

theorem gaL_star (hs : L.s = 0) (hQ : L.Q = ∅) (hc : ∀ g, star (c g) = c g) (φ : GA D V → ℂ) :
    gaL V β L eG c (star φ) = star (gaL V β L eG c φ) := by
  funext h
  have h1 : ∀ g, actG0 V β L (eG g) (star φ) h = star (actG0 V β L (eG g) φ h) := by
    intro g
    unfold actG0
    split_ifs with hk
    · simp [levChi_flag hs hQ]
    · simp
  simp only [gaL, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply, Pi.star_apply, star_sum,
    smul_eq_mul, star_mul', hc]
  exact Finset.sum_congr rfl fun g _ => congrArg _ (h1 g)

variable {eG c} {P : LevelP L.Pg L.r ℂ} {Pl0 : Type} {ok : Set Pl0} {pl : Pl0 → Pl D.host.E} {q : Pl0 → ℕ} {Sg : Pl0 → ℂ[X]}
  {X : Type} [AddCommGroup X] [Module ℂ X] {ρ : Representation ℂ (GfC V) X}

theorem fixed_of_killed (hs : L.s = 0) (hQ : L.Q = ∅) {x : X} (hx : x ∈ killed ρ (eqSet V β L eG c P ok pl q Sg))
    {k : GfC V} (hk : (k : GA D V) ∈ levG V β (flag1L L)) : ρ k x = x := by
  obtain ⟨h1, h2, -⟩ := mem_levi_flag_of_mem_parabolic hs hQ P hk
  have := mem_killed.1 hx _ (Or.inl (Or.inl ⟨k, h1, rfl⟩))
  simpa [h2, sub_eq_zero] using this

theorem isTopologicalGroup_GA (V : HSp D) : IsTopologicalGroup (GA D V) := by
  have : IsModuleTopology (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (AF D.host.F) _
  exact inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))

theorem isOpen_stab (hs : L.s = 0) (hQ : L.Q = ∅) {x : X} (hx : x ∈ killed ρ (eqSet V β L eG c P ok pl q Sg)) :
    IsOpen {g : GfC V | ρ g x = x} := by
  first
  | (rename_i h_5 h_6 h_16 h_17; revert D V β L G h_5 h_6 eG c P Pl0 ok pl q Sg X h_16 h_17 ρ hs hQ x hx; exact @_root_.GlobalTheory.FiniteRingMultiplication.isOpen_stabiliser)
  | exact @_root_.GlobalTheory.FiniteRingMultiplication.isOpen_stabiliser
  | exact _root_.GlobalTheory.FiniteRingMultiplication.isOpen_stabiliser
  | (apply _root_.GlobalTheory.FiniteRingMultiplication.isOpen_stabiliser <;> assumption)
  | (intros; apply _root_.GlobalTheory.FiniteRingMultiplication.isOpen_stabiliser <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FiniteRingMultiplication.isOpen_stabiliser <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FiniteRingMultiplication.isOpen_stabiliser ..)

theorem isGoodRep_of_killed (hs : L.s = 0) (hQ : L.Q = ∅) (hl : LiftsExist V β L)
    (h : killed ρ (eqSet V β L eG c P ok pl q Sg) ≠ ⊥) : IsGoodRep V β L eG c ρ := by
  obtain ⟨x, hx, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  choose κ hκ using fun g => hl (eG g)
  refine ⟨x, h0, fun k hk => fixed_of_killed hs hQ hx hk, fun g => ⟨κ g, (hκ g).1⟩, hκ, ?_⟩
  have := mem_killed.1 hx _ (Or.inl (Or.inr ⟨fun g => ⟨κ g, (hκ g).1⟩, hκ, rfl⟩))
  simpa [sub_eq_zero, map_sum, LinearMap.sum_apply] using this

end Level

section Hecke

variable {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {J : Subgroup (GA D V)} {Pl0 : Type} {ok : Set Pl0}
  {pl : Pl0 → Pl D.host.E} {q : Pl0 → ℕ}

theorem mem_hPart {Sg : Pl0 → ℂ[X]} {x : MMap M} : x ∈ hPart M J ok pl q Sg ↔
    ∀ P ∈ ok, ∀ k ≤ V.rank, ∀ α R, IsHeckeAt V (pl P) k α → Bridge.IsDC J α⁻¹ R →
      heckeOn M R x = ((Sg P).coeff k / ((-1) ^ k * (q P : ℂ) ^ (k * (k - 1) / 2))) • x := by
  simp only [hPart, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    sub_eq_zero]
  exact ⟨fun h P hP k hk α R ha hR => h P hP k hk α ha R hR, fun h P hP k hk α ha R hR => h P hP k hk α R ha hR⟩

theorem exists_conjModel {S' : D.what₂.Tau → SPar} (h : ∀ τ, S' τ = dualPar (S τ)) (M : DSModel V S) :
    ∃ (M' : DSModel V S') (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ),
      ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w, c τ (M'.rep τ g w) = M.rep τ g (c τ w) := by
  obtain rfl : S' = fun τ => dualPar (S τ) := funext h
  exact GlobalTheory.T.discrete_series_model_of_dual_parameter M

end Hecke

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}

theorem rank_zeroth_component_eq : (Yc D 0).rank = D.R.r := by
  rw [D.sp.Y_rank _ (min_le_right _ _), Nat.zero_min]
  simp [Ranks.rankY]

theorem rank_weight_component_eq (i : Fin D.R.m) : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2

theorem sign_at_base_place_eq_embedding (R : RealDat D A Ks) : sg0 D A = D.what₂.embLL := sgAt_mk _ R.hv0

theorem places (h : R.Char F) {P : Pl0} (hP : P ∈ A.ok A.μ0) :
    (∀ c : ℕ, (((D.host.g 0 * D.host.g 1) ^ c : ℕ) : 𝓞 D.host.E) ∉ (R.pl P).asIdeal) ∧
      (∀ c : ℕ, ((1 ^ c : ℕ) : 𝓞 D.host.E) ∉ (R.pl P).asIdeal) ∧
      (∀ PP ∈ R.Pg, PP ≠ R.pl P ∧ ¬ IsConjPl PP (R.pl P)) ∧ Bridge.SplitOff (R.pl P) ∅ := by
  have h1 := (GlobalTheory.PartsCompare.mem_ok_iff h P).1 hP
  have h2 : Bridge.SplitOff (R.pl P) (R.Pg : Set (Pl D.host.E)) :=
    ⟨h1.1, fun hh => h1.2.1 (h.fam.Sb hh), fun Q hQ => h1.2.2 Q (h.fam.Sb hQ)⟩
  obtain ⟨h3, h4, -⟩ := GlobalTheory.splitOff_places R.C.P R.Pg ∅ (R.pl P) h.lev.Pg (by simp) h2
  refine ⟨fun c hc => h3 ?_, fun c hc => ?_, h4, h1.1, by simp, by simp⟩
  · rw [Nat.cast_pow] at hc
    exact (R.pl P).isPrime.mem_of_pow_mem c hc
  · rw [one_pow, Nat.cast_one] at hc
    exact (R.pl P).isPrime.ne_top ((Ideal.eq_top_iff_one _).2 hc)

theorem unitary_rel (h : R.Char F) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) {Sg : Pl0 → ℂ[X]} {x : MMap (R.MW i σ)}
    (hx : x ∈ R.Wall i σ) (h0 : x ≠ 0)
    (hh : x ∈ hPart (R.MW i σ) (levG _ (R.βW i) (R.datWp i R.triv)) (A.ok A.μ0) R.pl A.q Sg) {P : Pl0} (hP : P ∈ A.ok A.μ0)
    (a : ℕ → ℂ) (ha : ∀ k, a k = (Sg P).coeff k / ((-1) ^ k * (A.q P : ℂ) ^ (k * (k - 1) / 2))) :
    a D.R.r ≠ 0 ∧ ∀ k ≤ D.R.r, star (a k) * a D.R.r = a (D.R.r - k) := by
  obtain ⟨c, hc⟩ := h.lev.βW i
  obtain ⟨-, p2, p3, p4⟩ := places h hP
  obtain ⟨hinj, hr, hip⟩ := h.models.HW i σ
  obtain ⟨y, rfl⟩ : x ∈ LinearMap.range (R.HW i σ).e := hr.symm ▸ hx
  have hy : y ≠ 0 := fun e => h0 (by rw [e, map_zero])
  have hne : ipM (R.MW i σ) (R.νW i) (R.fdW i) ((R.HW i σ).e y) ((R.HW i σ).e y) ≠ 0 := by
    intro e
    have := hip y y
    unfold ipAt at this
    rw [e, mul_zero, inner_self_eq_zero] at this
    exact hy this
  have hm : (R.HW i σ).e y ∈ Mult R.θ (R.MW i σ) (levG _ (R.βW i) (R.datWp i R.triv) : Set (GA D (Wc D i))) (fun _ => 1) :=
    mult_le R.θ _ (fun k hk => ⟨hk, (mem_levi_flag_of_mem_parabolic (L := R.datWp i R.triv) rfl rfl R.triv hk).2.2⟩) hx
  have := GlobalTheory.T.hecke_eigenvalue_at_base_frame R.θ (R.MW i σ) (R.βW i) (R.ΛW i) _ (R.datWp i R.triv) (R.pl P) (R.νW i) (R.fdW i) a _
    (h.models.νW i).1.1 (h.models.νW i).2 hc (p2 c)
    (fun P' hP' => p3 P' (hP'.resolve_right (Finset.notMem_empty _))) p4 hm hne
    (fun k hk α Rs h1 h2 => by rw [ha]; exact mem_hPart.1 hh P hP k hk α Rs h1 h2)
  rwa [rank_weight_component_eq] at this

theorem part_conj_eq {s : ℕ} (hs : A.fam.Ok s) (h : R.Char F) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (p : A.fam.base.Ix)
    {U : Submodule ℂ (MMap (R.MW i σ))} (hU : U ≤ R.Wall i σ) :
    U ⊓ hPart (R.MW i σ) (levG _ (R.βW i) (R.datWp i R.triv)) (A.ok A.μ0) R.pl A.q
        (fun P => (RealDat.polE (A := A) p.1 P).map (starRingEnd ℂ)) =
      U ⊓ hPart (R.MW i σ) (levG _ (R.βW i) (R.datWp i R.triv)) (A.ok A.μ0) R.pl A.q (RealDat.polW (A := A) p.1) := by
  ext x
  refine and_congr_right fun hx => ?_
  by_cases h0 : x = 0
  · subst h0
    exact ⟨fun _ => Submodule.zero_mem _, fun _ => Submodule.zero_mem _⟩
  have key : ∀ P ∈ A.ok A.μ0,
      (x ∈ hPart (R.MW i σ) (levG _ (R.βW i) (R.datWp i R.triv)) (A.ok A.μ0) R.pl A.q
        (fun P => (RealDat.polE (A := A) p.1 P).map (starRingEnd ℂ)) ∨
      x ∈ hPart (R.MW i σ) (levG _ (R.βW i) (R.datWp i R.triv)) (A.ok A.μ0) R.pl A.q (RealDat.polW (A := A) p.1)) →
      ∀ k ≤ (Wc D i).rank,
        ((RealDat.polE (A := A) p.1 P).map (starRingEnd ℂ)).coeff k / ((-1) ^ k * (A.q P : ℂ) ^ (k * (k - 1) / 2)) =
        (RealDat.polW (A := A) p.1 P).coeff k / ((-1) ^ k * (A.q P : ℂ) ^ (k * (k - 1) / 2)) := by
    intro P hP hor k hk
    have hq := GlobalTheory.PartsCompare.q_ne_zero hs hP
    rw [rank_weight_component_eq] at hk
    refine GlobalTheory.T.dual_polynomial_coefficients_eq (A.q P) D.R.r (RealDat.polE (A := A) p.1 P) _ _ hq (GlobalTheory.PartsCompare.polE_coeff_zero h p P)
      (GlobalTheory.T.family_polynomial_degree_le_rank R F hs h p P hP) (fun _ => rfl) (fun _ => by rw [← GlobalTheory.PartsCompare.polW_eq _ hq]) ?_ k hk
    exact hor.imp (fun e => unitary_rel h i σ (hU hx) h0 e hP _ fun _ => rfl)
      (fun e => unitary_rel h i σ (hU hx) h0 e hP _ fun _ => rfl)
  constructor
  · intro e
    refine mem_hPart.2 fun P hP k hk α Rs h1 h2 => ?_
    rw [← key P hP (Or.inl e) k hk]
    exact mem_hPart.1 e P hP k hk α Rs h1 h2
  · intro e
    refine mem_hPart.2 fun P hP k hk α Rs h1 h2 => ?_
    rw [key P hP (Or.inr e) k hk]
    exact mem_hPart.1 e P hP k hk α Rs h1 h2

theorem liftsY (h : R.Char F) : LiftsExist (Yc D 0) (R.βY 0) (R.dat0 R.triv) := by
  obtain ⟨c, hc⟩ := h.lev.βY 0 (lt_of_lt_of_le two_pos D.R.two_le_m)
  exact GlobalTheory.T.finite_group_lifts_to_parahoric_level _ _ _ _ _ hc rfl (GlobalTheory.T.typePlaces_not_pairwise_conjugate R.C.P R.Pg h.lev.Pg)

theorem liftsW (h : R.Char F) (i : Fin D.R.m) : LiftsExist (Wc D i) (R.βW i) (R.datWp i R.triv) := by
  obtain ⟨c, hc⟩ := h.lev.βW i
  exact GlobalTheory.T.finite_group_lifts_to_parahoric_level _ _ _ _ _ hc rfl (GlobalTheory.T.typePlaces_not_pairwise_conjugate R.C.P R.Pg h.lev.Pg)

theorem finrank_eq_of_multEq (h : R.Char F) (hD : CuspDecomp D) (hM : MultEq R) (i : Fin D.R.m)
    (M₀ : DSModel (Yc D 0) (parA (Ptw D) 0)) (P : LevelP R.Pg D.R.r ℂ) (Sg : Pl0 → ℂ[X])
    (f1 : FiniteDimensional ℂ (goodPart R.θ M₀ (levS _ (R.βY 0) (R.dat0 P)) (levChi _ (R.βY 0) (R.dat0 P)) R.e0 ⊓
      hPart M₀ (levG _ (R.βY 0) (R.dat0 R.triv)) (A.ok A.μ0) R.pl A.q Sg : Submodule ℂ (MMap M₀)))
    (f2 : FiniteDimensional ℂ (R.Wat i (sg0 D A) P ⊓
      hPart (R.MW i (sg0 D A)) (levG _ (R.βW i) (R.datWp i R.triv)) (A.ok A.μ0) R.pl A.q Sg :
        Submodule ℂ (MMap (R.MW i (sg0 D A))))) :
    Module.finrank ℂ (goodPart R.θ M₀ (levS _ (R.βY 0) (R.dat0 P)) (levChi _ (R.βY 0) (R.dat0 P)) R.e0 ⊓
      hPart M₀ (levG _ (R.βY 0) (R.dat0 R.triv)) (A.ok A.μ0) R.pl A.q Sg : Submodule ℂ (MMap M₀)) =
    Module.finrank ℂ (R.Wat i (sg0 D A) P ⊓
      hPart (R.MW i (sg0 D A)) (levG _ (R.βW i) (R.datWp i R.triv)) (A.ok A.μ0) R.pl A.q Sg :
        Submodule ℂ (MMap (R.MW i (sg0 D A)))) := by
  obtain ⟨c, hc⟩ := h.lev.βY 0 (lt_of_lt_of_le two_pos D.R.two_le_m)
  obtain ⟨c', hc'⟩ := h.lev.βW i
  have hrk : (Yc D 0).rank = (Wc D i).rank := rank_zeroth_component_eq.trans (rank_weight_component_eq i).symm
  obtain ⟨j, Φ, hΦ⟩ := GlobalTheory.T.exists_finiteAdelic_isometry_matching_frames (Yc D 0) (Wc D i) (R.βY 0) (R.ΛY 0) _ (R.βW i) (R.ΛW i) _ R.Pg hrk hc hc'
    (GlobalTheory.T.typePlaces_not_pairwise_conjugate R.C.P R.Pg h.lev.Pg)
  have e1 : (goodPart R.θ M₀ (levS _ (R.βY 0) (R.dat0 P)) (levChi _ (R.βY 0) (R.dat0 P)) R.e0 ⊓
      hPart M₀ (levG _ (R.βY 0) (R.dat0 R.triv)) (A.ok A.μ0) R.pl A.q Sg : Submodule ℂ (MMap M₀)) =
      allMaps R.θ M₀ ⊓ killed (finRep M₀) (eqSet (Yc D 0) (R.βY 0) (R.dat0 R.triv) R.eG
        (RealDat.eC (A := A) D.what₂.embLL) P (A.ok A.μ0) R.pl A.q Sg) :=
    GlobalTheory.T.goodForms_eq_killed_by_groupAlgebra R.θ M₀ (R.βY 0) (R.dat0 R.triv) R.eG _ P (A.ok A.μ0) R.pl A.q Sg rfl rfl (liftsY h)
  have e2 : (R.Wat i (sg0 D A) P ⊓
      hPart (R.MW i (sg0 D A)) (levG _ (R.βW i) (R.datWp i R.triv)) (A.ok A.μ0) R.pl A.q Sg :
        Submodule ℂ (MMap (R.MW i (sg0 D A)))) =
      allMaps R.θ (R.MW i (sg0 D A)) ⊓ killed (finRep (R.MW i (sg0 D A))) (eqSet (Wc D i) (R.βW i) (R.datWp i R.triv) R.eG
        (RealDat.eC (A := A) (sg0 D A)) P (A.ok A.μ0) R.pl A.q Sg) :=
    GlobalTheory.T.goodForms_eq_killed_by_groupAlgebra R.θ (R.MW i (sg0 D A)) (R.βW i) (R.datWp i R.triv) R.eG _ P (A.ok A.μ0) R.pl A.q Sg rfl rfl (liftsW h i)
  have e3 : RealDat.eC (A := A) (sg0 D A) = RealDat.eC (A := A) D.what₂.embLL := by rw [sign_at_base_place_eq_embedding R]
  have hl := GlobalTheory.T.isometry_matches_parahoric_levels (Yc D 0) (Wc D i) (R.βY 0) (R.βW i) D.R.r D.R.t (r_le_Y 0) (r_le_rank_Wc i) R.Pg R.chi
    (fun _ _ => 1) j Φ hΦ
  have e4 : killed ((finRep (R.MW i (sg0 D A))).comp Φ.toMulEquiv.toMonoidHom : Representation ℂ (GfC (Yc D 0)) _)
        (eqSet (Yc D 0) (R.βY 0) (R.dat0 R.triv) R.eG (RealDat.eC (A := A) D.what₂.embLL) P (A.ok A.μ0) R.pl A.q Sg) =
      killed (finRep (R.MW i (sg0 D A))) (eqSet (Wc D i) (R.βW i) (R.datWp i R.triv) R.eG
        (RealDat.eC (A := A) D.what₂.embLL) P (A.ok A.μ0) R.pl A.q Sg) :=
    GlobalTheory.T.levelTypeHecke_killed_correspond_matching_iso (Yc D 0) (Wc D i) (R.βY 0) (R.βW i) D.R.r D.R.t (r_le_Y 0) (r_le_rank_Wc i) R.Pg R.chi (fun _ _ => 1) Φ R.eG _ P
      (A.ok A.μ0) R.pl A.q Sg _ _ hrk (fun κ => (hl κ).1) (fun κ => (hl κ).2)
      (fun P0 hP0 => GlobalTheory.T.hecke_compat_finite_isometry (Yc D 0) (Wc D i) (R.βY 0) (R.ΛY 0) _ (R.βW i) (R.ΛW i) _ R.Pg j Φ (R.pl P0) hΦ hc hc'
        ((places h hP0).1 c) ((places h hP0).2.1 c'))
  rw [e1] at f1 ⊢
  rw [e2, e3, ← e4] at f2 ⊢
  refine GlobalTheory.T.finrank_killed_eq_of_equal_multiplicities _ _ _ (finRep M₀) _ _ _ _ (hD R.θ h.models.inf _ _ M₀)
    (GlobalTheory.T.irreducibleAdmissibleDecomposable_comp_equiv _ _ _ _ _ Φ (hD R.θ h.models.inf _ _ (R.MW i (sg0 D A)))) ?_
    (fun x hx => isOpen_stab rfl rfl hx) (fun x hx => isOpen_stab rfl rfl hx) f1 f2
  intro W _ _ σ h1 h2 h3
  rw [homInto_comp]
  exact hM i M₀ j Φ hΦ W σ h1 h2 (isGoodRep_of_killed rfl rfl (liftsY h) h3)

theorem star_levChi (b : Bool) {κ : GA D (Yc D 0)} (hκ : κ ∈ levS _ (R.βY 0) (R.dat0 (R.levR F b))) :
    levChi _ (R.βY 0) (R.dat0 (R.levL F b D.what₂.embLL)) κ = star (levChi _ (R.βY 0) (R.dat0 (R.levR F b)) κ) := by
  have hm : rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) κ) ∈ (R.levR F b).H := hκ.2.2
  have h1 := levChi_withP (β := R.βY 0) (L := R.dat0 R.triv) rfl rfl (R.levL F b D.what₂.embLL) κ
  have h2 := levChi_withP (β := R.βY 0) (L := R.dat0 R.triv) rfl rfl (R.levR F b) κ
  replace h2 := h2.trans (congrArg Units.val (extendOne_of_mem (P := (R.levR F b).H) (R.levR F b).chi hm))
  replace h1 := h1.trans (congrArg Units.val (extendOne_of_mem (P := (R.levL F b D.what₂.embLL).H) (R.levL F b D.what₂.embLL).chi hm))
  refine h1.trans (Eq.trans ?_ (congrArg star h2).symm)
  have h3 : (R.levL F b D.what₂.embLL).chi ⟨_, hm⟩ = ((R.levR F b).chi ⟨_, hm⟩)⁻¹ := by
    exact map_inv (Units.map D.what₂.embLL.toMonoidHom) _
  have h4 : IsOfFinOrder ((R.levR F b).chi ⟨_, hm⟩) := by
    have : Finite (G0 R.Pg D.R.r) := Finite.of_equiv _ R.eG.toEquiv
    exact MonoidHom.isOfFinOrder _ (isOfFinOrder_of_finite _)
  have h5 : ‖(((R.levR F b).chi ⟨_, hm⟩ : ℂˣ) : ℂ)‖ = 1 := ((Units.coeHom ℂ).isOfFinOrder h4).norm_eq_one
  rw [h3, Units.val_inv_eq_inv_val, Complex.inv_eq_conj h5]
  rfl

theorem finrank_parts {s : ℕ} (hs : A.fam.Ok s) (h : R.Char F) (hX : GoodStable A.X) (hD : CuspDecomp D) (hM : MultEq R)
    (b : Bool) (i : Fin D.R.m) (p : A.fam.base.Ix) :
    Module.finrank ℂ (R.Wat i (sg0 D A) (R.levL F b (sg0 D A)) ⊓
      hPart (R.MW i (sg0 D A)) (levG _ (R.βW i) (R.datWp i R.triv)) (A.ok A.μ0) R.pl A.q (RealDat.polW (A := A) p.1) :
        Submodule ℂ (MMap (R.MW i (sg0 D A)))) =
    Module.finrank ℂ (R.EEat (R.levR F b) ⊓
      hPart (R.MY 0) (levG _ (R.βY 0) (R.dat0 R.triv)) (A.ok A.μ0) R.pl A.q (RealDat.polE (A := A) p.1) :
        Submodule ℂ (MMap (R.MY 0))) := by
  obtain ⟨M₀, c, hc⟩ := exists_conjModel (S' := parA (Ptw D) 0)
    (fun τ => by rw [Nat.zero_min]; exact (dualPar_dualPar _).symm) (R.MY 0)
  have hW : R.Wat i (sg0 D A) (R.levL F b (sg0 D A)) ≤ R.Wall i (sg0 D A) :=
    (goodPart_le_flag (L := R.datWp i R.triv) R.θ _ rfl rfl _ _).trans inf_le_left
  have hE : R.EEat (R.levR F b) ≤ R.EEat R.triv := goodPart_le_flag (L := R.dat0 R.triv) R.θ _ rfl rfl _ _
  have hr := GlobalTheory.T.conjugate_models_multiplicity_equal R.θ (R.MY 0) M₀ c hc (levS _ (R.βY 0) (R.dat0 (R.levR F b))) (levChi _ (R.βY 0) (R.dat0 (R.levR F b)))
    (levChi _ (R.βY 0) (R.dat0 (R.levL F b D.what₂.embLL))) R.e0 R.e0 (levG _ (R.βY 0) (R.dat0 R.triv)) (A.ok A.μ0) R.pl A.q
    (RealDat.polE (A := A) p.1) (fun k hk => star_levChi b hk)
    (gaL_star (L := R.dat0 R.triv) R.eG _ rfl rfl (GlobalTheory.T.star_idemOf_coeff_eq_self D.what₂.embLL A.X hs.irr hX))
  have fE := (finrank_comap h.models.HE (U := R.EEat (R.levR F b) ⊓
      hPart (R.MY 0) (levG _ (R.βY 0) (R.dat0 R.triv)) (A.ok A.μ0) R.pl A.q (RealDat.polE (A := A) p.1))
      (inf_le_left.trans hE)).2
  have hl : R.levL F b (sg0 D A) = R.levL F b D.what₂.embLL := by rw [sign_at_base_place_eq_embedding R]
  rw [← part_conj_eq hs h i _ p hW]
  rw [hl] at hW ⊢
  have f1 : FiniteDimensional ℂ (goodPart R.θ M₀ (levS _ (R.βY 0) (R.dat0 (R.levL F b D.what₂.embLL)))
      (levChi _ (R.βY 0) (R.dat0 (R.levL F b D.what₂.embLL))) R.e0 ⊓
      hPart M₀ (levG _ (R.βY 0) (R.dat0 R.triv)) (A.ok A.μ0) R.pl A.q
        (fun P => (RealDat.polE (A := A) p.1 P).map (starRingEnd ℂ)) : Submodule ℂ (MMap M₀)) :=
    Module.rank_lt_aleph0_iff.1 (lt_of_eq_of_lt hr.symm (Module.rank_lt_aleph0_iff.2 fE))
  rw [← finrank_eq_of_multEq h hD hM i M₀ _ _ f1 (finrank_comap (h.models.HW i _) (inf_le_left.trans hW)).2]
  exact congrArg Cardinal.toNat hr.symm

theorem range_w0C (b : Bool) (i : Fin D.R.m) :
    LinearMap.range ((R.toCx F).w0C b i) = Tw.sub (twAt D.what₂.embLL A.v0) (R.WS F b i (sg0 D A)) := by
  have hpos : ((Real.sqrt (RealDat.nP F b) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (RealDat.nP_pos (F := F) b)).ne'
  have h3 : Submodule.span ℂ (Set.range fun k => (⟨R.bC F b i (sg0 D A) k, Submodule.subset_span ⟨k, rfl⟩⟩ :
      R.WS F b i (sg0 D A))) = ⊤ := Submodule.span_range_subtype_eq_top_iff _ _ |>.2 rfl
  have h4 : LinearMap.range ((R.toCx F).wC b i A.v0) = ⊤ := by
    have := Tw.span_top (E := R.WS F b i (sg0 D A)) (twAt D.what₂.embLL A.v0) h3
    rw [eq_top_iff]
    intro x _
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 (this.ge (Submodule.mem_top (x := x)))
    exact ⟨a, by rw [← ha]; exact Fintype.linearCombination_apply _ _ _⟩
  unfold CxData.w0C
  refine (LinearMap.range_comp_of_range_eq_top _ h4).trans ?_
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact (R.WS F b i (sg0 D A)).smul_mem _ (Tw.out (E := R.WS F b i (sg0 D A)) y).2
  · intro hx
    have hx' : Tw.out (s := twAt D.what₂.embLL A.v0) (E := (R.HW i (sg0 D A)).H) x ∈ R.WS F b i (sg0 D A) := hx
    refine ⟨Tw.mk (E := R.WS F b i (sg0 D A)) (twAt D.what₂.embLL A.v0)
      (((Real.sqrt (RealDat.nP F b) : ℝ) : ℂ)⁻¹ • ⟨_, hx'⟩), ?_⟩
    show ((Real.sqrt (RealDat.nP F b) : ℝ) : ℂ) • (((Real.sqrt (RealDat.nP F b) : ℝ) : ℂ)⁻¹ •
      Tw.out (s := twAt D.what₂.embLL A.v0) (E := (R.HW i (sg0 D A)).H) x) =
      Tw.out (s := twAt D.what₂.embLL A.v0) (E := (R.HW i (sg0 D A)).H) x
    rw [smul_smul, mul_inv_cancel₀ hpos, one_smul]

theorem dimParts_level (R : RealDat D A Ks) (F : Face D A) {s : ℕ} (hs : A.fam.Ok s) (h : R.Char F) (hX : GoodStable A.X)
    (hL : R.LLevelW F) (hD : CuspDecomp D) (hM : MultEq R) (b : Bool) : (R.toCx F).DimParts b := by
  intro i p
  have hW : R.Wat i (sg0 D A) (R.levL F b (sg0 D A)) ≤ R.Wat i (sg0 D A) R.triv :=
    goodPart_le_flag (L := R.datWp i R.triv) R.θ _ rfl rfl _ _
  have hE : R.EEat (R.levR F b) ≤ R.EEat R.triv := goodPart_le_flag (L := R.dat0 R.triv) R.θ _ rfl rfl _ _
  have e1 : (R.toCx F).Wp i p ⊓ LinearMap.range ((R.toCx F).w0C b i) = Tw.sub (twAt D.what₂.embLL A.v0)
      ((R.Wat i (sg0 D A) (R.levL F b (sg0 D A)) ⊓
        hPart (R.MW i (sg0 D A)) (levG _ (R.βW i) (R.datWp i R.triv)) (A.ok A.μ0) R.pl A.q
          (RealDat.polW (A := A) p.1)).comap (R.HW i (sg0 D A)).e) := by
    rw [range_w0C, hL b i (sg0 D A)]
    ext x
    exact ⟨fun hx => ⟨hx.2, hx.1.2⟩, fun hx => ⟨⟨hW hx.1, hx.2⟩, hx.1⟩⟩
  have e2 : (R.toCx F).EEp p ⊓ (R.toCx F).EEl b = Tw.sub (twAt D.what₂.embLL A.v0)
      ((R.EEat (R.levR F b) ⊓
        hPart (R.MY 0) (levG _ (R.βY 0) (R.dat0 R.triv)) (A.ok A.μ0) R.pl A.q (RealDat.polE (A := A) p.1)).comap R.HE.e) := by
    ext x
    exact ⟨fun hx => ⟨hx.2, hx.1⟩, fun hx => ⟨hx.2, hx.1⟩⟩
  rw [e1, e2]
  exact (finrank_twSub (E := (R.HW i (sg0 D A)).H) _ _).trans
    ((finrank_comap (h.models.HW i (sg0 D A)) (inf_le_left.trans (hW.trans inf_le_left))).1.trans
      ((finrank_parts hs h hX hD hM b i p).trans
        ((finrank_comap h.models.HE (inf_le_left.trans hE)).1.symm.trans (finrank_twSub (E := R.HE.H) _ _).symm)))

theorem dimParts (R : RealDat D A Ks) (F : Face D A) {s : ℕ} (hs : A.fam.Ok s) (h : R.Char F) (hX : GoodStable A.X)
    (hL : R.LLevelW F) (hD : CuspDecomp D) (hM : MultEq R) : (R.toCx F).DimParts false :=
  dimParts_level R F hs h hX hL hD hM false

end GlobalTheory.PartDims

end
