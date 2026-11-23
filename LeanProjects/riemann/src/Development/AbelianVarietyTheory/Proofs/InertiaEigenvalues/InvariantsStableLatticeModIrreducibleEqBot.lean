import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoboundaryMemBlochKatoCocycles
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NatCastPowNeZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankSplit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsComplOfSaturated

noncomputable section

namespace GlobalTheory.TopSteps.FinSummand

open Module TensorProduct
open GlobalTheory.AdmLoc Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N

theorem exists_isCompl_of_saturated {O M : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
    [AddCommGroup M] [Module O M] [Module.Finite O M] (N : Submodule O M)
    (h : ∀ (a : O) (x : M), a ≠ 0 → a • x ∈ N → x ∈ N) : ∃ C : Submodule O M, IsCompl N C := by
  first
  | exact @_root_.GlobalTheory.SaturatedComplement.exists_isCompl_of_saturated
  | exact _root_.GlobalTheory.SaturatedComplement.exists_isCompl_of_saturated
  | (apply _root_.GlobalTheory.SaturatedComplement.exists_isCompl_of_saturated <;> assumption)
  | (intros; apply _root_.GlobalTheory.SaturatedComplement.exists_isCompl_of_saturated <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SaturatedComplement.exists_isCompl_of_saturated <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SaturatedComplement.exists_isCompl_of_saturated ..)

theorem codim_eq_card {L M : Type} [Field L] [AddCommGroup M] [Module L M] (F : ℤ → Submodule L M)
    (U : Submodule L M) [FiniteDimensional L U] (anti : Antitone F) (hle : ∀ a, F a ≤ U)
    (exh : ∀ x ∈ U, ∃ a, x ∈ F a) (J : Multiset ℤ)
    (h : ∀ a, (finrank L (F a) : ℤ) - finrank L (F (a + 1)) = (J.count a : ℤ)) (c : ℤ) :
    (finrank L U : ℤ) - finrank L (F c) = (Multiset.card (J.filter (· < c)) : ℤ) := by
  classical
  obtain ⟨s, hs⟩ : U.FG := Module.Finite.iff_fg.1 inferInstance
  have hm : ∀ x : s, ∃ a, (x : M) ∈ F a := fun x => exh x (hs ▸ Submodule.subset_span x.2)
  choose f hf using hm
  obtain ⟨b₁, hb₁⟩ := (Set.finite_range f).bddBelow
  obtain ⟨b₂, hb₂⟩ := J.toFinset.bddBelow
  have hb : F (min (min b₁ b₂) c) = U := by
    refine le_antisymm (hle _) ?_
    rw [← hs, Submodule.span_le]
    intro x hx
    exact anti ((min_le_left _ _).trans ((min_le_left _ _).trans (hb₁ ⟨⟨x, hx⟩, rfl⟩))) (hf ⟨x, hx⟩)
  have key : ∀ a, min (min b₁ b₂) c ≤ a →
      (finrank L U : ℤ) - finrank L (F a) = (Multiset.card (J.filter (· < a)) : ℤ) := by
    intro a ha
    induction a, ha using Int.le_induction with
    | base =>
      rw [hb, sub_self, Multiset.filter_eq_nil.2]
      · simp
      · intro u hu
        have : b₂ ≤ u := hb₂ (by simpa using hu)
        have h1 := min_le_left (min b₁ b₂) c
        have h2 := min_le_right b₁ b₂
        omega
    | succ a _ ih =>
      have h1 : J.filter (· < a + 1) = J.filter (· < a) + J.filter (a = ·) := by
        ext u
        simp only [Multiset.count_add, Multiset.count_filter]
        split_ifs <;> omega
      have h2 := h a
      rw [h1, Multiset.card_add, ← Multiset.count_eq_card_filter_eq]
      push_cast
      omega
  exact key c (min_le_right _ _)

section General

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL]

section Rep

variable {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
  {ρ : Representation LL G V}

omit [TopologicalSpace G] in

theorem codim_fil_zero {n : ℕ} [NeZero n] (emb : ZMod n → (K₀ →ₐ[Qp] LL)) (hemb : Function.Bijective emb)
    (hK : Function.Bijective (algebraMap K₀ K)) (hn : n = finrank Qp K)
    [Module.Finite LL ↥(DdR PD ρ)] (U : ZMod n → Multiset ℤ) (hU : ∀ i, HasJumps PD ρ (emb i) (U i)) :
    (finrank LL ↥(DdR PD ρ) : ℤ) - finrank LL ↥(DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) 0) =
      ∑ i, (Multiset.card ((U i).filter (· < 0)) : ℤ) := by
  let E : K₀ ≃ₐ[Qp] K := AlgEquiv.ofBijective (IsScalarTower.toAlgHom Qp K₀ K) hK
  let e : ZMod n ≃ (K →ₐ[Qp] LL) := (Equiv.ofBijective emb hemb).trans (E.arrowCongr AlgEquiv.refl)
  have he : ∀ i x, e i (algebraMap K₀ K x) = emb i x := fun i x => by
    change emb i (E.symm (E x)) = emb i x
    rw [AlgEquiv.symm_apply_apply]
  letI : Fintype (K →ₐ[Qp] LL) := Fintype.ofEquiv _ e
  have hcard : Fintype.card (K →ₐ[Qp] LL) = finrank Qp K := by
    rw [← Fintype.card_congr e, ZMod.card, hn]
  obtain ⟨h1, h2⟩ := GlobalTheory.DeRhamSplit.finrank_split PD hcard ρ
  rw [h1, h2 0, Nat.cast_sum, Nat.cast_sum, ← Finset.sum_sub_distrib, ← e.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  haveI : FiniteDimensional LL ↥(DdRE PD ρ (e i)) :=
    Submodule.finiteDimensional_of_le (S₂ := DdR PD ρ) inf_le_left
  exact codim_eq_card (FildR PD ρ (e i)) (DdRE PD ρ (e i))
    (fun a b hab => inf_le_inf_left _ (GlobalTheory.Cmp.SmallJumps.filV_anti PD hab)) (fun a => inf_le_left)
    (fun x hx => (GlobalTheory.Cmp.SmallJumps.filV_exh PD (LL := LL) x).imp fun _ ha => ⟨hx, ha⟩) (U i)
    (hU i (e i) (he i)) 0

variable [Module O V] [IsScalarTower O LL V] [IsDomain O] [IsFractionRing O LL]

omit [TopologicalSpace G] in

theorem invariants_stableLattice_mod_irreducible_eq_bot [IsDiscreteValuationRing O] (L : Lattice (O := O) ρ) {lam : O} (hlam : Irreducible lam)
    (h : (coefRep (latRep L) (O ⧸ Ideal.span {lam})).invariants = ⊥) : H0V ρ = ⊥ := by
  haveI : Module.Finite O ↥L.T := Module.Finite.iff_fg.2 L.fg
  have hsm : ∀ (a : O) (x : V), a ≠ 0 → a • x = 0 → x = 0 := fun a x ha hx => by
    rw [← algebraMap_smul LL] at hx
    exact (smul_eq_zero.1 hx).resolve_left (by simpa using ha)
  have hM : (latRep L).invariants = ⊥ := by
    refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (Ideal.span {lam}) _ (IsNoetherian.noetherian _) ?_ ?_
    · intro x hx
      have h1 : x ⊗ₜ[O] (1 : O ⧸ Ideal.span {lam}) ∈
          (coefRep (latRep L) (O ⧸ Ideal.span {lam})).invariants := fun g => by
        rw [coefRep_tmul, hx g]
      rw [h, Submodule.mem_bot] at h1
      have h2 := congrArg (TensorProduct.tensorQuotEquivQuotSMul ↥L.T (Ideal.span {lam})) h1
      rw [map_zero, ← map_one (Ideal.Quotient.mk _), TensorProduct.tensorQuotEquivQuotSMul_tmul_mk, one_smul,
        Submodule.Quotient.mk_eq_zero, Submodule.ideal_span_singleton_smul] at h2
      obtain ⟨y, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists x lam ⊤).1 h2
      refine Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) fun g => Subtype.ext ?_
      have h3 := congrArg Subtype.val (hx g)
      rw [map_smul] at h3
      refine sub_eq_zero.1 (hsm lam _ hlam.ne_zero ?_)
      rw [smul_sub]
      exact sub_eq_zero.2 h3
    · rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, hlam.maximalIdeal_eq]
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨a, ha, hax⟩ := GlobalTheory.H1fGeneratorBoundAlt.exists_smul_mem L x
  have h1 : (⟨a • x, hax⟩ : ↥L.T) ∈ (latRep L).invariants := fun g => Subtype.ext (by
    have := (Submodule.mem_iInf _).1 hx g
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at this
    change ρ g (a • x) = a • x
    rw [← algebraMap_smul LL, map_smul, this])
  rw [hM, Submodule.mem_bot] at h1
  exact hsm a x ha (congrArg Subtype.val h1)

variable [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]

theorem h1fT_saturated (L : Lattice (O := O) ρ) (a : O) (x : LatticeCohomology L) (ha : a ≠ 0) (hx : a • x ∈ latticeFiniteCohomology PD L) :
    x ∈ latticeFiniteCohomology PD L := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨c', hc', h⟩ := hx
  rw [← Submodule.Quotient.mk_smul, Submodule.mkQ_apply, Submodule.Quotient.eq] at h
  obtain ⟨b, -, hb⟩ := h
  have h1 : ((c' - a • c : ↥(latticeCocycles L)) : G → V) ∈ finiteCocycles PD ρ := by
    refine ⟨(c' - a • c).2.1, b ⊗ₜ 1, fun g => ?_⟩
    have : ρ g b - b = ((c' - a • c : ↥(latticeCocycles L)) : G → V) g := congrFun hb g
    rw [← this]
    simp [actVB, sub_tmul]
  have h2 : algebraMap O LL a • (c : G → V) ∈ finiteCocycles PD ρ := by
    have := (finiteCocycles PD ρ).sub_mem hc'.2 h1
    rw [algebraMap_smul]
    simpa using this
  have ha' : algebraMap O LL a ≠ 0 := by simpa using ha
  have h3 : (c : G → V) ∈ finiteCocycles PD ρ := (Submodule.smul_mem_iff (finiteCocycles PD ρ) ha').1 h2
  exact ⟨c, ⟨c.2, h3⟩, rfl⟩

theorem finrank_h1fT [CompactSpace G] (L : Lattice (O := O) ρ) (hT : IsOpen (L.T : Set V)) :
    finrank O ↥(latticeFiniteCohomology PD L) = finrank LL (FiniteCohomology PD ρ) := by
  refine congrArg Cardinal.toNat (GlobalTheory.BlochKatoRank.rank_subquotient_eq (K := LL) LinearMap.id (latticeCocycles L) (latticeCoboundaries L)
    (latticeFiniteCocycles PD L) (finiteCocycles PD ρ) (B1 ρ) (fun a ha => ha.2) ?_ ?_ ?_)
  · rintro _ ⟨x, -, rfl⟩
    exact ⟨x, rfl⟩
  · rintro a ⟨x, hx⟩
    obtain ⟨m, hm, h⟩ := GlobalTheory.H1fGeneratorBoundAlt.exists_smul_mem L x
    refine ⟨m, hm, m • x, h, ?_⟩
    rw [map_smul]
    exact congrArg (m • ·) hx
  · intro c hc
    obtain ⟨a, ha, h⟩ := GlobalTheory.H1fGeneratorBoundAlt.exists_smul_fun_mem L hT c hc.1.1
    have h1 : a • c ∈ (finiteCocycles PD ρ).restrictScalars O :=
      Submodule.smul_mem ((finiteCocycles PD ρ).restrictScalars O) a hc
    exact ⟨a, ha, a • c, ⟨h1.1, fun g _ => h g⟩, ⟨⟨h1.1, fun g _ => h g⟩, h1⟩, rfl⟩

end Rep

theorem summand_of_crys [TopologicalSpace Qp] [TopologicalSpace LL] [CompactSpace G]
    (hO : GoodO (Qp := Qp) LL O) (hBK : Formalism.MainNotions.LocalSituation.bkADim PD) (hF : Formalism.MainNotions.LocalSituation.fontCore PD)
    {n : ℕ} [NeZero n] (emb : ZMod n → (K₀ →ₐ[Qp] LL)) (hemb : Function.Bijective emb)
    (hK : Function.Bijective (algebraMap K₀ K)) (hn : n = finrank Qp K) (T : LocLat G Qp LL O)
    (hT : IsOpen (T.L.T : Set T.V)) (U : ZMod n → Multiset ℤ) (hU : CrysWith PD emb T.ρ U)
    {lam : O} (hlam : Irreducible lam)
    (h0 : (coefRep (latRep T.L) (O ⧸ Ideal.span {lam})).invariants = ⊥) (hfin : Module.Finite O (LatticeCohomology T.L)) :
    (∃ C : Submodule O (LatticeCohomology T.L), IsCompl (latticeFiniteCohomology PD T.L) C) ∧
      finrank O ↥(latticeFiniteCohomology PD T.L) = ∑ i, Multiset.card ((U i).filter (· < 0)) := by
  obtain ⟨_, _, _⟩ := hO.1
  refine ⟨exists_isCompl_of_saturated _ (h1fT_saturated PD T.L), ?_⟩
  let A : GRep G Qp LL O := { V := T.V, ρ := T.ρ, cont := T.cont }
  obtain ⟨-, ⟨hD, -⟩, hdR⟩ := hF LL O hO A
  haveI : Module.Finite LL ↥(DdR PD T.ρ) := hD
  have h1 : (finrank LL (FiniteCohomology PD T.ρ) : ℤ) = finrank LL ↥(H0V T.ρ) +
      ((finrank LL ↥(DdR PD T.ρ) : ℤ) - finrank LL ↥(DdR PD T.ρ ⊓ FilV PD (LL := LL) (V := T.V) 0)) :=
    hBK LL O hO A (hdR hU.1)
  rw [invariants_stableLattice_mod_irreducible_eq_bot T.L hlam h0, finrank_bot, codim_fil_zero PD emb hemb hK hn U hU.2, Nat.cast_zero,
    zero_add] at h1
  rw [finrank_h1fT PD T.L hT]
  exact_mod_cast h1

theorem summand_of_gal [TopologicalSpace Qp] [TopologicalSpace LL] [CompactSpace G]
    (hO : GoodO (Qp := Qp) LL O) (hBK : Formalism.MainNotions.LocalSituation.bkADim PD) (hF : Formalism.MainNotions.LocalSituation.fontCore PD)
    {n r : ℕ} [NeZero n] (emb : ZMod n → (K₀ →ₐ[Qp] LL)) (hemb : Function.Bijective emb)
    (hK : Function.Bijective (algebraMap K₀ K)) (hn : n = finrank Qp K) (D : TopData n r)
    (Γ : GalData G Qp LL O) (hT : IsOpen (Γ.T₀.L.T : Set Γ.T₀.V))
    (hχ : Continuous fun g => algebraMap O LL (Γ.χ₁⁻¹ g))
    (hU : CrysWith PD emb (twistRep Γ.T₀.ρ (chiLL LL Γ.χ₁⁻¹)) (fun i => (D.U i).map (· + -D.w i)))
    (hlam : Irreducible Γ.lam) (h0 : (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.resRep Γ).invariants = ⊥)
    (hfin : Module.Finite O (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.HH Γ)) :
    (∃ C : Submodule O (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.HH Γ), IsCompl (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.Hf PD Γ) C) ∧
      finrank O ↥(GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.Hf PD Γ) = D.dsum := by
  have h := summand_of_crys PD hO hBK hF emb hemb hK hn (twLat Γ.T₀ Γ.χ₁⁻¹ hχ) hT _ hU hlam
    (by
      change (coefRep (latRep (twLattice Γ.T₀.L Γ.χ₁⁻¹)) (O ⧸ Ideal.span {Γ.lam})).invariants = ⊥
      rw [latRep_twLattice]
      exact h0) hfin
  refine ⟨h.1, h.2.trans (Finset.sum_congr rfl fun i _ => ?_)⟩
  rw [Multiset.filter_map, Multiset.card_map, TopData.d]
  exact congrArg _ (Multiset.filter_congr fun u _ => by simp)

end General

open GlobalTheory.PhiGam GlobalTheory.Models GlobalTheory.TopSteps in

theorem fSummand : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (S : TopSit P), Formalism.MainNotions.LocalSituation.bkADim (P.PD S.K) → Formalism.MainNotions.LocalSituation.fontCore (P.PD S.K) → S.CrysCalc → S.Vanish → S.FreeH → S.FSummand := by
  intro l _ P AI _ S hBK hF hC hV hH
  obtain ⟨⟨-, hA, hn, hemb, -, hlam⟩, ⟨-, hρ, hχ, -⟩, -⟩ := S.hyp
  have hO := (GlobalTheory.LocalIntegers.good_integers l S.LL).1
  haveI := GlobalTheory.BlochKatoIntegralScalars.compactSpace_GK S.K
  have h1 := (hC.2.1 S.Γ.T₀ S.D.U S.Γ.χ₁ S.D.w hρ hχ).2
  have h2 := (hC.2.1 S.Γ.T₀ S.D.U S.Γ.χ₁⁻¹ _ hρ h1).1
  have hK : Function.Bijective (algebraMap ↥(K0 S.K) ↥S.K.1) :=
    ⟨RingHom.injective _, fun x => ⟨⟨x.1, x.2, hA.1 x.2⟩, rfl⟩⟩
  exact summand_of_gal (P.PD S.K) hO hBK hF S.emb hemb hK hn S.D S.Γ (GlobalTheory.Cyc.locLat_isOpen hO S.Γ.T₀) h1.1 h2
    hlam hV.1 hH.1.2.1

end GlobalTheory.TopSteps.FinSummand
