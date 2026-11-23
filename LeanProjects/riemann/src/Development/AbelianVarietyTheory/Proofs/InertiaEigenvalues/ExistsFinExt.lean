import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusIsDomainBdRIsField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCyclotomicChar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAlgEquivRootOfUnityEqPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLogTeichmullerAcrisEqMuMulUnit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisLogTeichmullerUniqueGaloisFrobeniusBdR
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootOfUnityPrimeToTeichmullerLift
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisIncl

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.FitsEx

theorem exists_lift {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (i : B →+* C)
    (hi : Function.Injective i) (f : A →+* C) (h : ∀ x, ∃ y, f x = i y) :
    ∃ g : A →+* B, ∀ x, i (g x) = f x := by
  choose g hg using h
  exact ⟨{ toFun := g
           map_one' := hi (by rw [← hg, map_one, map_one])
           map_mul' := fun x y => hi (by rw [map_mul, ← hg, ← hg, ← hg, map_mul])
           map_zero' := hi (by rw [← hg, map_zero, map_zero])
           map_add' := fun x y => hi (by rw [map_add, ← hg, ← hg, ← hg, map_add]) }, fun x => (hg x).symm⟩

variable {l : ℕ} [Fact l.Prime]

theorem eps_root {P : LocPrime l} (AI : LocAinf l P) (m : ℕ) :
    (rootT (l := l) AI.ε m : ℂ_[l]) = algebraMap (Om l) ℂ_[l] (P.ζQ m) := by
  have : rootT (l := l) AI.ε m = AI.ζ m := by
    refine Perfection.teichmuller_spec (I := Ideal.span {(l : Per.OC l)}) fun n => ?_
    refine ⟨AI.ζ (m + n), ?_, by rw [zeta_pow_iter AI.ζ_succ]⟩
    have := zeta_coeff_root_iterate (p := l) (O := Per.OC l) AI.ε m n
    rw [add_comm] at this
    exact (AI.ε_coeff (m + n)).symm.trans this.symm
  rw [this]
  exact AI.ζ_eq m

theorem isLog_unique {e : Per.Fl l} (he : e.untilt = 1) {y y' : Per.BdRp l}
    (h : Per.IsLog l e y) (h' : Per.IsLog l e y') :
    y = y' :=
  GlobalTheory.CrisIncl.log_unique l e he y y' h h'

theorem exists_finExt (x : Om l) : ∃ K : FinExt l, x ∈ K.1 :=
  ⟨⟨IntermediateField.adjoin ℚ_[l] {x},
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)⟩,
    IntermediateField.mem_adjoin_simple_self _ x⟩

theorem iota_alg (P : LocPrime l) (c : ↥(MaximalUnramifiedExtension l)) :
    P.ιB (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c) = algebraMap (Om l) P.R.BdR (c : Om l) := by
  obtain ⟨K, hK⟩ := exists_finExt (c : Om l)
  rw [← P.PD_ι K]
  exact (P.PD K).ι.commutes (⟨c, hK, c.2⟩ : ↥(K0 K))

theorem iota_inj (P : LocPrime l) : Function.Injective P.ιB := by
  obtain ⟨K, -⟩ := exists_finExt (0 : Om l)
  intro a b h
  exact (P.PD K).ι_inj (by rw [P.PD_ι, P.PD_ι, h])

theorem phi_alg {P : LocPrime l} (AI : LocAinf l P) (σ : ↥(MaximalUnramifiedExtension l) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l))
    (hσ : ∀ (c : ↥(MaximalUnramifiedExtension l)) (m : ℕ), 0 < m → ¬ l ∣ m → c ^ m = 1 → σ c = c ^ l) (c : ↥(MaximalUnramifiedExtension l)) :
    P.φB (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c) = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (σ c) := by
  have key : P.φB.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(MaximalUnramifiedExtension l) P.R.B) =
      (IsScalarTower.toAlgHom ℚ_[l] ↥(MaximalUnramifiedExtension l) P.R.B).comp σ := by
    refine IntermediateField.algHom_ext_of_eq_adjoin ℚ_[l] (S := MaximalUnramifiedExtension l) rfl fun x hx => ?_
    obtain ⟨m, hm, hlm, hxm⟩ := id hx
    obtain ⟨xb, hxb⟩ := exists_isTiltOf x m hm hlm hxm
    have hx' : x ∈ MaximalUnramifiedExtension l := IntermediateField.subset_adjoin _ _ hx
    have h1 := AI.ιA_teich ⟨x, hx'⟩ m hm hlm hxm xb hxb
    change P.φB (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B ⟨x, hx'⟩) = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (σ ⟨x, hx'⟩)
    rw [hσ ⟨x, hx'⟩ m hm hlm (Subtype.ext hxm), map_pow, ← h1, ← AI.ιA_φ, ← map_pow,
      WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, map_pow]
  exact DFunLike.congr_fun key c

theorem sigma_eq {P : LocPrime l} (AI : LocAinf l P) (σ : ↥(MaximalUnramifiedExtension l) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l))
    (hσ : ∀ (c : ↥(MaximalUnramifiedExtension l)) (m : ℕ), 0 < m → ¬ l ∣ m → c ^ m = 1 → σ c = c ^ l)
    (K : FinExt l) (x : ↥(K0 K)) (c : ↥(MaximalUnramifiedExtension l)) (h : (c : Om l) = (x : Om l)) :
    (((P.PD K).σ x : ↥(K0 K)) : Om l) = ((σ c : ↥(MaximalUnramifiedExtension l)) : Om l) := by
  have : Nontrivial P.R.B := by
    refine ⟨⟨1, 0, fun h0 => one_ne_zero (AI.ιA_inj ?_)⟩⟩
    rw [map_one, map_zero, h0]
  have h1 := (P.PD K).φ_K₀ x
  rw [P.PD_φ] at h1
  have hc : c = ⟨x, x.2.2⟩ := Subtype.ext h
  have h2 := phi_alg AI σ hσ c
  rw [hc] at h2 ⊢
  have h3 : algebraMap ↥(MaximalUnramifiedExtension l) P.R.B ⟨((P.PD K).σ x : ↥(K0 K)), ((P.PD K).σ x).2.2⟩ = _ := h1.symm.trans h2
  exact congrArg Subtype.val ((algebraMap ↥(MaximalUnramifiedExtension l) P.R.B).injective h3)

theorem zeta_prim (P : LocPrime l) (m : ℕ) : IsPrimitiveRoot (P.ζQ (m + 1)) (l ^ (m + 1)) := by
  have h0 := zeta_pow_iter P.ζQ_succ 0 (m + 1)
  rw [zero_add, P.ζQ_zero] at h0
  have h1 := zeta_pow_iter P.ζQ_succ 1 m
  rw [add_comm] at h1
  have := orderOf_eq_prime_pow (x := P.ζQ (m + 1)) (p := l) (n := m) (by rw [h1]; exact P.ζQ_one) h0
  rw [← this]
  exact IsPrimitiveRoot.orderOf _

theorem chi_eq (P : LocPrime l) (χ : GQ l →* ℤ_[l]ˣ)
    (hχ : ∀ (g : GQ l) (m : ℕ) (x : Om l), x ^ (l ^ m) = 1 → g x = x ^ (PadicInt.toZModPow m (χ g : ℤ_[l])).val)
    (g : GQ l) : ((P.χQ g : ℚ_[l]ˣ) : ℚ_[l]) = (((χ g : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) := by
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have key : ∀ m : ℕ, ‖((P.χQ g : ℚ_[l]ˣ) : ℚ_[l]) - (((χ g : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l])‖ ≤
      (l : ℝ) ^ (-((m + 1 : ℕ) : ℤ)) := by
    intro m
    have hp := zeta_prim P m
    obtain ⟨a, ha, hg⟩ := P.χQ_cyc g (m + 1) _ hp.pow_eq_one
    rw [hχ g (m + 1) _ hp.pow_eq_one] at hg
    have hmod : (PadicInt.toZModPow (m + 1) (χ g : ℤ_[l])).val ≡ a [MOD l ^ (m + 1)] := by
      have hfin : IsOfFinOrder (P.ζQ (m + 1)) :=
        isOfFinOrder_iff_pow_eq_one.2 ⟨_, pow_pos (Fact.out : l.Prime).pos _, hp.pow_eq_one⟩
      have := hfin.pow_eq_pow_iff_modEq.1 hg
      rwa [← hp.eq_orderOf] at this
    have hk : ((a : ℤ_[l]) - (χ g : ℤ_[l])) ∈ Ideal.span {(l : ℤ_[l]) ^ (m + 1)} := by
      rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast,
        ← (ZMod.natCast_eq_natCast_iff _ _ _).2 hmod]
      have : NeZero (l ^ (m + 1)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
      rw [ZMod.natCast_zmod_val, sub_self]
    have hn := (PadicInt.norm_le_pow_iff_mem_span_pow _ _).2 hk
    have hn' : ‖(a : ℚ_[l]) - (((χ g : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l])‖ ≤ (l : ℝ) ^ (-((m + 1 : ℕ) : ℤ)) := by
      simpa [PadicInt.norm_def] using hn
    rw [← sub_add_sub_cancel _ (a : ℚ_[l])]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hn')
  by_contra hne
  have hpos := norm_pos_iff.2 (sub_ne_zero.2 hne)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hpos (inv_lt_one_of_one_lt₀ hl)
  have h1 := key n
  rw [zpow_neg, zpow_natCast, ← inv_pow] at h1
  have h2 : (l : ℝ)⁻¹ ^ (n + 1) ≤ (l : ℝ)⁻¹ ^ n :=
    pow_le_pow_of_le_one (by positivity) (inv_lt_one_of_one_lt₀ hl).le (Nat.le_succ n)
  linarith

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

theorem exists_fits : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI),
    ∃ C : Core l, Fits T C := by
  intro l _ P AI T
  have hinj := (BdRField.bdR_isField l).2.1
  obtain ⟨o, ho⟩ := exists_lift _ hinj (T.eD.toRingHom.comp (algebraMap (Om l) P.R.BdR))
    fun x => (T.om x).imp fun _ h => h.1
  have hosec : IsSec o := by
    refine ⟨fun x => ?_, fun z => hinj ?_⟩
    · obtain ⟨y, hy, hy'⟩ := T.om x
      rw [← hy', hinj ((ho x).trans hy)]
    · rw [ho]
      change T.eD (algebraMap (Om l) P.R.BdR _) = _
      rw [← IsScalarTower.algebraMap_apply, T.zD]
      exact GlobalTheory.RingIface.zD_eq_alg l z
  have hincl := T.incl
  set ι := (T.eD.toRingHom.comp (P.ιB : P.R.B →+* P.R.BdR)).comp T.eB.symm.toRingHom with hι
  have hιe : ∀ b : P.R.B, T.eD (P.ιB b) = ι (T.eB b) := fun b => by simp [hι]
  clear_value ι
  obtain ⟨j, hj', hj0, hjb⟩ := GlobalTheory.CrisIncl.exists_restrict l ι hincl
  have hj : ∀ x, algebraMap (Per.BdRp l) (Per.BdR l) (j x) =
      (ι.comp (algebraMap (Per.Acris l) (Per.Bcris l))) x := fun x => (hj' x).symm
  have hjc : IsCrisP j := ⟨hj0, hjb⟩
  have he : PreTilt.untilt (AI.ε : Per.Fl l) = 1 := Subtype.ext (by
    have := eps_root AI 0
    rw [P.ζQ_zero, map_one] at this
    exact this)
  obtain ⟨t, -, ht, -⟩ := exists_isLogA l AI.ε he
  obtain ⟨σ, hσ⟩ := exists_frobenius_Kur l
  obtain ⟨χ, hχ⟩ := exists_cyclotomicChar l
  refine ⟨{ ζ := P.ζQ, ζ_zero := P.ζQ_zero, ζ_succ := P.ζQ_succ, ζ_one := P.ζQ_one
            ε := AI.ε, ε_root := eps_root AI, o := o, o_sec := hosec, j := j, j_cris := hjc
            ι := ι, ι_j := fun x => (hj x).symm
            u := T.eB.toRingHom.comp (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B)
            ι_u := fun c => ?_
            t := t, t_log := ht, σ := σ, σ_root := hσ, χ := χ, χ_cyc := hχ },
    ⟨rfl, rfl, fun x => (ho x).symm, hιe, fun _ => rfl, ?_, chi_eq P χ hχ, sigma_eq AI σ hσ⟩⟩
  · rw [ho]
    exact (hιe _).symm.trans (congrArg T.eD (iota_alg P c))
  · obtain ⟨y, hy, hy'⟩ := T.t
    have h1 := isLog_unique he hy ((LogFun.log_fun l AI.ε t he ht).2.2.2 j hjc)
    have h2 : T.eD (P.ιB P.tB) = T.eD (P.ιB (T.eB.symm (algebraMap (Per.Acris l) (Per.Bcris l) t))) := by
      rw [hy', h1, hj, hιe, RingEquiv.apply_symm_apply]
      rfl
    rw [iota_inj P (T.eD.injective h2), RingEquiv.apply_symm_apply]
    rfl

end GlobalTheory.MemLoc.FitsEx
