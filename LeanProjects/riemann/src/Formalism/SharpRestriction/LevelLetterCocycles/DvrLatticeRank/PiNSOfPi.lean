import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.LevelValueSmul
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.DescentValuation
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ConstantCoeffQZeroEqP
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.GradNPfB

noncomputable section

namespace Formalism.MainNotions.N.Ln34.LevelExpansions

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.N.Ln34 Formalism.MainNotions.N.Ln34.DescentValuation TensorProduct

section Val

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

abbrev rest (T : LocLat G Qp LL O) (τ : K →ₐ[Qp] LL) : Submodule LL (T.V ⊗[Qp] BdR) :=
  ⨆ (τ' : K →ₐ[Qp] LL) (_ : τ' ≠ τ), DdRE PD T.ρ τ'

theorem fildR_gap (T : LocLat G Qp LL O) (τ : K →ₐ[Qp] LL) (a b : ℤ) (hab : a ≤ b)
    (hj : ∀ i, a ≤ i → i < b → ¬ IsJumpV PD T.ρ τ i) : FildR PD T.ρ τ b = FildR PD T.ρ τ a := by
  induction b, hab using Int.le_induction with
  | base => rfl
  | succ b hb ih =>
    have hn := hj b hb (by omega)
    unfold IsJumpV at hn
    rw [not_not] at hn
    rw [hn, ih fun i h1 h2 => hj i h1 (by omega)]

theorem filC_top (T : LocLat G Qp LL O) (τ : K →ₐ[Qp] LL) (a : ℤ)
    (hj : ∀ i, a ≤ i → ¬ IsJumpV PD T.ρ τ i) {z : T.V ⊗[Qp] BdR}
    (hz : z ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ a) : z ∈ rest (PD := PD) T τ := by
  have h0 : FildR PD T.ρ τ a = ⊥ := by
    refine (Submodule.eq_bot_iff _).2 fun w hw => CrystallineExponents.filV_sep PD (LL := LL) w fun b => ?_
    rcases le_total a b with h | h
    · rw [← fildR_gap T τ a b h fun i h1 _ => hj i h1] at hw
      exact (Submodule.mem_inf.1 hw).2
    · exact CrystallineExponents.filVB_anti PD h (Submodule.mem_inf.1 hw).2
  unfold Formalism.MainNotions.DeltaInvariantLattices.FilC at hz
  rwa [h0, bot_sup_eq] at hz

variable (W : LocWach PD LL O v n)

theorem ιDi_inf_rest (T : LocLat G Qp LL O) (c : ZMod n) (ζ : LL) (τ : K →ₐ[Qp] LL)
    (h41 : ∀ (x : ↥(W.N T)) (k : ℤ), W.levN T c ζ ((letE c : LetA O n) • x) k ∈
      Formalism.MainNotions.DeltaInvariantLattices.ιDi W T c ⊓ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (-k))
    (h42 : ∀ (k : ℤ), ∀ w ∈ FildR PD T.ρ τ (-k), ∃ (x : ↥(W.N T)) (a : LL), a ≠ 0 ∧
      (∀ j < k, a • W.levN T c ζ ((letE c : LetA O n) • x) j ∈
        Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (-j + 1)) ∧
      a • W.levN T c ζ ((letE c : LetA O n) • x) k - w ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (-k + 1))
    [FiniteDimensional LL ↥(Formalism.MainNotions.DeltaInvariantLattices.ιDi W T c)] [FiniteDimensional LL ↥(DdRE PD T.ρ τ)]
    (hdim : finrank LL ↥(Formalism.MainNotions.DeltaInvariantLattices.ιDi W T c) ≤ finrank LL ↥(DdRE PD T.ρ τ)) :
    Formalism.MainNotions.DeltaInvariantLattices.ιDi W T c ⊓ rest (PD := PD) T τ = ⊥ := by
  set I := Formalism.MainNotions.DeltaInvariantLattices.ιDi W T c with hI
  set R := rest (PD := PD) T τ with hR
  set D := DdRE PD T.ρ τ with hD
  obtain ⟨a₀, h₀⟩ := CrystallineExponents.exists_le_filV PD D
  obtain ⟨a₁, h₁⟩ := CrystallineExponents.exists_inf_filV_eq_bot PD D
  have key : ∀ d : ℕ, FildR PD T.ρ τ (a₁ - d) ≤ I ⊔ R := by
    intro d
    induction d with
    | zero =>
      have : FildR PD T.ρ τ (a₁ - ((0 : ℕ) : ℤ)) = ⊥ := by
        rw [Nat.cast_zero, sub_zero]; exact h₁
      rw [this]; exact bot_le
    | succ d ih =>
      intro w hw
      obtain ⟨x, a, -, -, hk⟩ := h42 (-(a₁ - ((d + 1 : ℕ) : ℤ))) w (by rwa [neg_neg])
      rw [show -(-(a₁ - ((d + 1 : ℕ) : ℤ))) + 1 = a₁ - d by push_cast; ring] at hk
      have h2 : Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (a₁ - d) ≤ I ⊔ R := sup_le ih le_sup_right
      have h3 := Submodule.sub_mem _ (Submodule.mem_sup_left (T := R)
        (I.smul_mem a (Submodule.mem_inf.1 (h41 x (-(a₁ - ((d + 1 : ℕ) : ℤ))))).1)) (h2 hk)
      rwa [sub_sub_cancel] at h3
  have hDI : D ≤ I ⊔ R := by
    intro w hw
    refine key (a₁ - a₀).toNat ⟨hw, CrystallineExponents.filVB_anti PD ?_ (h₀ hw)⟩
    have := Int.self_le_toNat (a₁ - a₀)
    omega
  have hDR : D ⊓ R = ⊥ := CrystallineExponents.ddRE_inf_rest T τ
  have hker : ∀ S : Submodule LL (T.V ⊗[Qp] BdR),
      LinearMap.ker (R.mkQ ∘ₗ S.subtype) = ⊥ ↔ S ⊓ R = ⊥ := by
    intro S
    rw [LinearMap.ker_comp, Submodule.ker_mkQ, ← Submodule.disjoint_iff_comap_eq_bot, disjoint_iff]
  have hr1 := LinearMap.finrank_range_add_finrank_ker (R.mkQ ∘ₗ D.subtype)
  rw [(hker D).2 hDR, finrank_bot, add_zero] at hr1
  have hr2 := LinearMap.finrank_range_add_finrank_ker (R.mkQ ∘ₗ I.subtype)
  have hle : LinearMap.range (R.mkQ ∘ₗ D.subtype) ≤ LinearMap.range (R.mkQ ∘ₗ I.subtype) := by
    rintro _ ⟨w, rfl⟩
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 (hDI w.2)
    refine ⟨⟨y, hy⟩, ?_⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, Submodule.mkQ_apply]
    rw [Submodule.Quotient.eq, ← hyz]
    simpa using hz
  have hr3 := Submodule.finrank_mono hle
  rw [← hker, ← Submodule.finrank_eq_zero]
  omega

structure ValH (T : LocLat G Qp LL O) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (π' : LetA O n)
    (c : ZMod n) : Prop where
  add : ∀ τ ζ, Pt c ζ τ → ∀ x ∈ NcS W T (c - 1), ∀ y ∈ NcS W T (c - 1),
    valAt W T c ζ (x + y) = valAt W T c ζ x + valAt W T c ζ y
  smul : ∀ τ ζ, Pt c ζ τ → ∀ (o : O), ∀ x ∈ NcS W T (c - 1),
    valAt W T c ζ (o • x) = algebraMap O LL o • valAt W T c ζ x
  indep : ∀ τ ζ τ' ζ', Pt c ζ τ → Pt c ζ' τ' → ∀ x ∈ NcS W T (c - 1), valAt W T c ζ x = valAt W T c ζ' x
  ker : ∀ τ ζ, Pt c ζ τ → ∀ x ∈ NcS W T (c - 1), valAt W T c ζ x = 0 ↔ x ∈ PiNS W T π' 1
  wd : ∀ τ ζ, Pt c ζ τ → ∀ {m m' : ℕ} (a : Fin m → LetA O n) (y : Fin m → W.DD T)
    (hy : ∀ j, y j ∈ NcS W T (c - 1)) (b : Fin m' → LetA O n) (z : Fin m' → W.DD T)
    (hz : ∀ k, z k ∈ NcS W T (c - 1)),
    ∑ j, algebraMap (LetA O n) W.EE ((letE c : LetA O n) * a j) ⊗ₜ[O] mkL W T π' c (y j) (hy j) =
      ∑ k, algebraMap (LetA O n) W.EE ((letE c : LetA O n) * b k) ⊗ₜ[O] mkL W T π' c (z k) (hz k) →
    expS W T c ζ a y = expS W T c ζ b z
  fil : ∀ τ ζ, Pt c ζ τ → ∀ x ∈ NcS W T (c - 1),
    ∃ k : ℤ, valAt W T c ζ x ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ k
  inj : ∀ τ ζ, Pt c ζ τ → ∀ x ∈ NcS W T (c - 1),
    valAt W T c ζ x ∈ rest (PD := PD) T τ → valAt W T c ζ x = 0

variable {W}

theorem ValH.sum {T : LocLat G Qp LL O} {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop} {π' : LetA O n}
    {c : ZMod n} (H : ValH W T Pt π' c) {τ : K →ₐ[Qp] LL} {ζ : LL} (hpt : Pt c ζ τ) {ι : Type}
    (s : Finset ι) (o : ι → O) (y : ι → W.DD T) (hy : ∀ j, y j ∈ NcS W T (c - 1)) :
    valAt W T c ζ (∑ j ∈ s, o j • y j) = ∑ j ∈ s, algebraMap O LL (o j) • valAt W T c ζ (y j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have := H.smul τ ζ hpt 0 0 (Submodule.zero_mem _)
    simpa using this
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, H.add τ ζ hpt _ (Submodule.smul_mem _ _ (hy j)) _
      (Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hy k)), H.smul τ ζ hpt _ _ (hy j), ih]

theorem φVB_inj' (T : LocLat G Qp LL O) : Function.Injective (φVB PD (LL := LL) (V := T.V)) := by
  have h : ∀ y, φVB PD (LL := LL) (V := T.V) y = (PD.φ.toLinearMap.lTensor T.V) y := fun y => by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul x b => simp [φVB]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hi : Function.Injective PD.φ.toLinearMap := PD.φ_inj
  intro a b hab
  rw [h, h] at hab
  exact Module.Flat.lTensor_preserves_injective_linearMap _ hi hab

theorem piNS_of_pi (T : LocLat G Qp LL O) {e s' : ℕ} {π' π₀ : LetA O n} {E : ZMod n → Polynomial O}
    (hp9 : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W e s' π' E) (hπ0 : ∀ i, PowerSeries.constantCoeff (π' i) = 0)
    (hm : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T π₀) {x : W.DD T} (hx : x ∈ W.NΔ T)
    (hπ : x ∈ Formalism.MainNotions.DeltaInvariantLattices.aN W T letπ) : x ∈ PiNS W T π' 1 := by
  obtain ⟨⟨r, b, hb, hu, hΔ⟩, -⟩ := hm
  obtain ⟨a, ha, hxa⟩ := hΔ x hx
  obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.1 hπ
  have hyx' : (letπ : LetA O n) • y = x := hyx
  obtain ⟨a', hya, -⟩ := hu y hy
  have h2 : x = ∑ j, (letπ * a' j) • b j := by
    rw [← hyx', hya, Finset.smul_sum]
    exact Finset.sum_congr rfl fun j _ => smul_smul _ _ _
  have he := (hu x hx.1).unique hxa h2
  have ht : ∀ j, ∃ t : LetA O n, a j = π' * t := by
    intro j
    obtain ⟨F, hF, -⟩ := hp9.2.1 (a j) (ha j)
    obtain ⟨t, ht⟩ := gradNPf_expand π' (a j) hπ0 F hF 0 (fun i => by
      rw [he]
      simp [letπ])
    exact ⟨t, by simpa using ht⟩
  choose t ht using ht
  refine (mem_PiNS W T π' 1 x).2 ⟨⟨∑ j, t j • b j,
    Submodule.sum_mem _ fun j _ => (W.N T).smul_mem _ (hb j).1, ?_⟩, hx.2⟩
  rw [hxa, Finset.smul_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [pow_one, smul_smul, ht j]

variable {Zl Ai : Type} [CommRing Zl] [CommRing Ai] [Algebra Zl O] [Algebra Zl Ai]
    {RW : Type} [CommRing RW] [Algebra O RW]
    {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai}
    {Et : EtTie W (O ⊗[Zl] Ai) RW inclR φR gR πA} {ιdR : Ai →+* BdR} {p1 : Ai} {tS zS : BdR}

theorem valH_of (Ct : CmpTie W Et ιdR p1 tS zS) [IsDedekindDomain O]
    (hinj : Function.Injective (algebraMap O LL)) (T : LocLat G Qp LL O)
    (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (c : ZMod n) (hs : W.s = 1) (hc : IsCrys PD T.ρ)
    (hprim : ∀ τ ζ, Pt c ζ τ → IsPrimitiveRoot ζ PD.p)
    {e s' : ℕ} {π' π₀ : LetA O n} {E : ZMod n → Polynomial O}
    (hp9 : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W e s' π' E) (hs1 : 1 ≤ s') (hm : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T π₀)
    (h3 : Formalism.MainNotions.DeltaInvariantLattices.p3 W T) (h4 : Formalism.MainNotions.DeltaInvariantLattices.p4 W Pt T)
    [FiniteDimensional LL ↥(Formalism.MainNotions.DeltaInvariantLattices.ιDi W T c)] (hfd : ∀ τ, FiniteDimensional LL ↥(DdRE PD T.ρ τ))
    (hdim : ∀ τ, finrank LL ↥(Formalism.MainNotions.DeltaInvariantLattices.ιDi W T c) ≤ finrank LL ↥(DdRE PD T.ρ τ)) :
    ValH W T Pt π' c := by
  obtain ⟨w, hw⟩ := hp9.2.2.1
  have hone : ∃ j : ℕ, IsPrimitiveRoot (1 : LL) (PD.p ^ j) := ⟨0, by simp⟩
  have hπ1 : ∀ i, PowerSeries.constantCoeff (W.lev i 1 letπ) = 0 := fun i => by
    rw [CrystallineExponents.cc_lev_pi W i 1 hone, sub_self]
  have hπ : PowerSeries.constantCoeff (W.lev (c - 1) 1 π') = 0 := by
    rw [hw, map_mul, map_pow, map_mul, map_pow, hπ1, zero_pow (by omega), mul_zero]
  have hπ0 : ∀ i, PowerSeries.constantCoeff (π' i) = 0 := fun i => by
    have : π' i = (w : LetA O n) i * PowerSeries.X ^ s' := by rw [hw]; rfl
    rw [this, map_mul, map_pow, PowerSeries.constantCoeff_X, zero_pow (by omega), mul_zero]
  have hX : W.X = letπ := by simp [LocWach.X, hs]
  have hP : ∀ τ ζ, Pt c ζ τ → V.PtHyp (W := W) T c ζ := by
    intro τ ζ hpt
    have hz := hprim τ ζ hpt
    obtain ⟨hQ0, hQ1⟩ := framepf_Q_at W hs c ζ hz
    refine ⟨hc, ⟨1, by simpa using hz⟩, hz.pow_eq_one, hQ0, hQ1, fun x k hk => ?_, fun x hx => W.N_φ T x hx⟩
    exact (((h4.1 (c - 1) 1 ⟨0, one_pow _⟩ (by rw [hX]; exact hπ1 _)).1 x k).2 hk)
  refine ⟨fun τ ζ hpt x hx y hy => ?_, fun τ ζ hpt o x hx => ?_, fun τ ζ τ' ζ' hpt hpt' x hx => ?_,
    fun τ ζ hpt x hx => ⟨fun h0 => ?_, fun hx' => ?_⟩,
    fun τ ζ hpt m m' a y hy b z hz h => V.expS_wd Ct T hinj (hP τ ζ hpt) π' hπ a y hy b z hz h,
    fun τ ζ hpt x hx => u3downPf_valAt_fil W T c ζ τ (h4.2 c ζ τ hpt).2.1 x hx,
    fun τ ζ hpt x hx hr => ?_⟩
  · exact (V.valL Ct T (hP τ ζ hpt)).map_add ⟨x, hx⟩ ⟨y, hy⟩
  · exact (V.valL Ct T (hP τ ζ hpt)).map_smul o ⟨x, hx⟩
  · have hxN := ((mem_NcS W T (c - 1) x).1 hx).1
    exact (V.valAt_eq Ct T (hP τ ζ hpt) ⟨x, hxN⟩).trans (V.valAt_eq Ct T (hP τ' ζ' hpt') ⟨x, hxN⟩).symm
  · obtain ⟨hxN, hxΔ, hxc⟩ := (mem_NcS W T (c - 1) x).1 hx
    have h1 := (V.valAt_eq Ct T (hP τ ζ hpt) ⟨x, hxN⟩).symm.trans h0
    unfold V.val1 at h1
    have h2 := φVB_inj' T ((framepf_ιV_inj (PD := PD) T (h1.trans (map_zero _).symm)).trans
      (map_zero _).symm)
    rw [← Ct.cmp_eq T hc] at h2
    have h5 := h3.1 _ h2
    have h6 : (((letE (c - 1) : LetA O n) • (⟨x, hxN⟩ : ↥(W.N T)) : ↥(W.N T)) : W.DD T) = x := hxc
    rw [h6] at h5
    exact piNS_of_pi T hp9 hπ0 hm ⟨hxN, hxΔ⟩ h5
  · exact V.valL_ker Ct T (hP τ ζ hpt) π' hπ (x := ⟨x, hx⟩) hx'
  · have := hfd τ
    have hb := ιDi_inf_rest W T c ζ τ (h4.2 c ζ τ hpt).2.1 (h4.2 c ζ τ hpt).2.2 (hdim τ)
    have hI : valAt W T c ζ x ∈ Formalism.MainNotions.DeltaInvariantLattices.ιDi W T c := by
      classical
      have hxN := ((mem_NcS W T (c - 1) x).1 hx).1
      unfold valAt
      split_ifs with h
      · exact Submodule.smul_mem _ _ ((h4.2 c ζ τ hpt).1.1 ⟨x, hxN⟩ _ (Nat.find_spec h) _).1
      · exact Submodule.zero_mem _
    have : valAt W T c ζ x ∈ Formalism.MainNotions.DeltaInvariantLattices.ιDi W T c ⊓ rest (PD := PD) T τ := ⟨hI, hr⟩
    rwa [hb, Submodule.mem_bot] at this

end Val

end Formalism.MainNotions.N.Ln34.LevelExpansions

end
