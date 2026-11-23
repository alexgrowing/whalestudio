import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.LocEig
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.OrdA

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al
section LocEigAux
open UpperTheory.V.Hi UpperTheory.V.AlgebraTools
private theorem antitone_mem : ∀ {n : ℕ} (M : AddSubmonoid (Fin n → ℤ)), (∀ j ≤ n, fund n j ∈ M) → (-1 : Fin n → ℤ) ∈ M →
    ∀ a : Fin n → ℤ, Antitone a → a ∈ M := by
  intro n M h1 h2 a ha
  cases n with
  | zero =>
    have : a = 0 := Subsingleton.elim _ _
    rw [this]
    exact zero_mem _
  | succ N =>
    have hone : (1 : Fin (N + 1) → ℤ) ∈ M := by
      have := h1 (N + 1) le_rfl
      convert this using 1
      funext i
      simp [fund, i.2]
    let A : ℕ → ℤ := fun m => a ⟨min m N, by omega⟩
    have hA : ∀ m, A (m + 1) ≤ A m := fun m => ha (by
      simp only [Fin.mk_le_mk]
      omega)
    have tel : ∀ (m i : ℕ), i ≤ m → ∑ j ∈ Finset.range m, (if i < j + 1 then A j - A (j + 1) else 0) = A i - A m := by
      intro m
      induction m with
      | zero =>
        intro i hi
        obtain rfl : i = 0 := by omega
        simp
      | succ m ih =>
        intro i hi
        rw [Finset.sum_range_succ]
        by_cases h : i ≤ m
        · rw [ih i h, if_pos (by omega)]
          ring
        · obtain rfl : i = m + 1 := by omega
          rw [if_neg (by omega), Finset.sum_eq_zero]
          · simp
          · intro j hj
            have := Finset.mem_range.1 hj
            rw [if_neg (by omega)]
    have key : a = (A N) • (1 : Fin (N + 1) → ℤ) + ∑ j ∈ Finset.range N, (A j - A (j + 1)).toNat • fund (N + 1) (j + 1) := by
      funext i
      have hi : A i = a i := by
        show a _ = a i
        congr 1
        ext
        have := i.2
        simp only
        omega
      have h3 : ∀ j ∈ Finset.range N, (A j - A (j + 1)).toNat • fund (N + 1) (j + 1) i =
          if (i : ℕ) < j + 1 then A j - A (j + 1) else 0 := by
        intro j _
        have : (((A j - A (j + 1)).toNat : ℕ) : ℤ) = A j - A (j + 1) := Int.toNat_of_nonneg (sub_nonneg.2 (hA j))
        simp only [fund, nsmul_eq_mul, this]
        split_ifs <;> simp
      have h4 := tel N i (by have := i.2; omega)
      simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one, Finset.sum_apply]
      rw [Finset.sum_congr rfl h3, h4, hi]
      ring
    rw [key]
    refine add_mem ?_ (sum_mem fun j hj => nsmul_mem (h1 _ (by have := Finset.mem_range.1 hj; omega)) _)
    obtain ⟨m, e | e⟩ := (A N).eq_nat_or_neg
    · rw [e, natCast_zsmul]
      exact nsmul_mem hone m
    · rw [e, neg_smul, ← smul_neg, natCast_zsmul]
      exact nsmul_mem h2 m
private theorem u_operator_torus_eigen {G : Type} [Group G] (I : Iwa G) {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    (π : Representation A G M) {t : G} (ht : t ∈ I.T) {v : M} (hv : v ∈ fixd π I.N) {c : A} (hc : π t v = c • v) :
    I.uOp π t v = c • v := by
  have h : (I.Nconj t).subgroupOf I.N = ⊤ := by
    rw [Subgroup.subgroupOf_eq_top]
    intro x hx
    refine ⟨t⁻¹ * x * t, by simpa using I.T_N t⁻¹ (inv_mem ht) x hx, ?_⟩
    show t * (t⁻¹ * x * t) * t⁻¹ = x
    group
  haveI : Subsingleton (I.N ⧸ (I.Nconj t).subgroupOf I.N) := by
    rw [h]
    exact QuotientGroup.subsingleton_quotient_top
  letI := Unique.mk' (I.N ⧸ (I.Nconj t).subgroupOf I.N)
  rw [Iwa.uOp, finsum_unique, map_mul, Module.End.mul_apply, hc, map_smul, hv _ (SetLike.coe_mem _)]
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
private noncomputable def mu (ψ : Fin n → kˣ →* ℂˣ) (i : Fin n) : kˣ →* ℂˣ :=
  ψ i * (absPow k ((modExp (fun _ : Fin n => Unit) i : ℂ) / 2))⁻¹
private theorem expo_eq (ψ : Fin n → kˣ →* ℂˣ) (d : Fin n → kˣ) : Dict.expo ψ d = ((torusChar (mu ψ) d : ℂˣ) : ℂ) := by
  have hd : ∀ i, Matrix.GeneralLinearGroup.det (leviTorus k (Fin n) d i) = d i :=
    congrFun ((leviTorus k (Fin n)).left_inv d)
  simp [Dict.expo, deltaHalf_apply, hd, mu, Finset.prod_mul_distrib]
private noncomputable def omg (ψ : Fin n → kˣ →* ℂˣ) (i : Fin n) : kˣ →* ℂˣ := ψ i * absPow k (-(((n : ℂ) - 1) / 2))
private theorem om_shift (ψ : Fin n → kˣ →* ℂˣ) : (fun i => omg ψ i * absPow k (((n : ℂ) - 1) / 2)) = ψ := by
  funext i
  rw [omg, mul_assoc, ← absPow_add, neg_add_cancel, absPow_zero, mul_one]
private theorem om_unit (ψ : Fin n → kˣ →* ℂˣ) (i : Fin n) {y : kˣ} (hy : valuation k (y : k) = 1) : omg ψ i y = ψ i y := by
  simp [omg, isUnram_absPow k _ y hy]
private theorem mu_unit (ψ : Fin n → kˣ →* ℂˣ) (i : Fin n) {y : kˣ} (hy : valuation k (y : k) = 1) : mu ψ i y = ψ i y := by
  simp [mu, isUnram_absPow k _ y hy]
private theorem mu_unif (ψ : Fin n → kˣ →* ℂˣ) (i : Fin n) :
    (mu ψ i (UpperTheory.V.Hi.unif k) : ℂ) = (omg ψ i (UpperTheory.V.Hi.unif k) : ℂ) * ((Nat.card 𝓀[k] : ℂ) ^ (i : ℕ))⁻¹ := by
  have hq : nabs k (UpperTheory.V.Hi.unif k) = (Nat.card 𝓀[k] : ℝ)⁻¹ := GlobalTheory.GLDoubling.nabs_unif GlAx.unif_spec
  have e : mu ψ i = omg ψ i * absPow k ((i : ℕ) : ℂ) := by
    have hi := i.2
    rw [mu, omg, mul_assoc, ← absPow_add, ← absPow_neg, modExp_fin _ (fun _ => by simp)]
    congr 2
    push_cast
    ring
  rw [e, MonoidHom.mul_apply, Units.val_mul, val_absPow, hq, Complex.cpow_natCast]
  simp
private theorem mu_fund (ψ : Fin n → kˣ →* ℂˣ) (j : ℕ) :
    ((torusChar (mu ψ) (fun i => UpperTheory.V.Hi.unif k ^ fund n j i) : ℂˣ) : ℂ) = psEig (omg ψ) j := by
  rw [torusChar_apply, Units.coe_prod, psEig, Finset.prod_filter]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases h : (i : ℕ) < j
  · simp only [fund, if_pos h, zpow_one]
    exact mu_unif ψ i
  · simp [fund, if_neg h]
private theorem diagT_inj : Function.Injective (diagT k (Fin n)) := by
  intro s t h
  funext i
  have := congrArg (fun g : GL (Fin n) k => (g : Matrix (Fin n) (Fin n) k) i i) h
  simp only [val_diagT, Matrix.diagonal_apply_eq] at this
  exact Units.ext this
private noncomputable def phi (ω : Fin n → kˣ →* ℂˣ) : (glIwa k n).T →* ℂˣ :=
  ((torusChar ω)⁻¹ : (Fin n → kˣ) →* ℂˣ).comp ((torusO k (Fin n)).subtype.comp
    ((torusO k (Fin n)).equivMapOfInjective (diagT k (Fin n)) diagT_inj).symm.toMonoidHom)
private theorem phi_diag (ω : Fin n → kˣ →* ℂˣ) (u : Fin n → kˣ) (hu : u ∈ torusO k (Fin n)) :
    phi ω ⟨diagT k (Fin n) u, u, hu, rfl⟩ = (torusChar ω u)⁻¹ := by
  have : ((torusO k (Fin n)).equivMapOfInjective (diagT k (Fin n)) diagT_inj).symm ⟨diagT k (Fin n) u, u, hu, rfl⟩ = ⟨u, hu⟩ := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  exact congrArg (fun x : torusO k (Fin n) => (torusChar ω (x : Fin n → kˣ))⁻¹) this
private theorem phi_inv (ω : Fin n → kˣ →* ℂˣ) : IsInvOn (phi ω) ω := by
  intro i y
  have hu : (Pi.mulSingle i (y : kˣ) : Fin n → kˣ) ∈ torusO k (Fin n) := fun j => by
    by_cases h : j = i
    · subst h
      rw [Pi.mulSingle_eq_same]
      exact y.2
    · simp [Pi.mulSingle_eq_of_ne h]
  refine (phi_diag ω _ hu).trans ?_
  rw [torusChar_apply, Fintype.prod_eq_single i (fun j hj => by simp [Pi.mulSingle_eq_of_ne hj])]
  simp
private theorem upow_add (a b : Fin n → ℤ) : upow k n (a + b) = upow k n a * upow k n b := by
  rw [upow, upow, upow, ← map_mul]
  congr 1
  funext i
  simp [_root_.zpow_add]
private theorem upow_mem {a : Fin n → ℤ} (ha : Antitone a) : upow k n a ∈ (glIwa k n).P := ⟨a, ha, rfl⟩
private theorem uOp_upow {T : Type} [AddCommGroup T] [Module ℂ T] (τ : Representation ℂ (GL (Fin n) k) T)
    (ψ : Fin n → kˣ →* ℂˣ) {v : T} (hv : v ∈ fixd τ (glIwa k n).N)
    (hev : ∀ j ≤ n, (glIwa k n).uOp τ (al k n j) v = psEig (omg ψ) j • v) (a : Fin n → ℤ) (ha : Antitone a) :
    (glIwa k n).uOp τ (upow k n a) v = ((torusChar (mu ψ) (fun i => UpperTheory.V.Hi.unif k ^ a i) : ℂˣ) : ℂ) • v := by
  have E_add : ∀ a b : Fin n → ℤ, torusChar (mu ψ) (fun i => UpperTheory.V.Hi.unif k ^ (a + b) i) =
      torusChar (mu ψ) (fun i => UpperTheory.V.Hi.unif k ^ a i) * torusChar (mu ψ) (fun i => UpperTheory.V.Hi.unif k ^ b i) := by
    intro a b
    rw [← map_mul]
    congr 1
    funext i
    simp [_root_.zpow_add]
  have E_zero : torusChar (mu ψ) (fun i => UpperTheory.V.Hi.unif k ^ (0 : Fin n → ℤ) i) = 1 := by
    have : (fun i => UpperTheory.V.Hi.unif k ^ (0 : Fin n → ℤ) i) = 1 := by
      funext i
      simp
    rw [this, map_one]
  have mulOp := fun x y hx hy => (uOpMul _ (glIwa k n) ℂ T τ x y hx hy v hv)
  let M : AddSubmonoid (Fin n → ℤ) :=
    { carrier := {a | Antitone a ∧ (glIwa k n).uOp τ (upow k n a) v =
        ((torusChar (mu ψ) (fun i => UpperTheory.V.Hi.unif k ^ a i) : ℂˣ) : ℂ) • v}
      add_mem' := by
        rintro a b ⟨ha, ea⟩ ⟨hb, eb⟩
        refine ⟨ha.add hb, ?_⟩
        rw [upow_add, ← (mulOp _ _ (upow_mem ha) (upow_mem hb)).2.1, eb, map_smul, ea, smul_smul, E_add, Units.val_mul,
          mul_comm]
      zero_mem' := by
        refine ⟨fun _ _ _ => le_rfl, ?_⟩
        have h1 : upow k n (0 : Fin n → ℤ) = 1 := by
          rw [upow, ← (diagT k (Fin n)).map_one]
          congr 1
          funext i
          simp
        rw [h1, E_zero, (mulOp 1 1 (one_mem _) (one_mem _)).2.2.1]
        simp }
  have hfund : ∀ j ≤ n, fund n j ∈ M := by
    intro j hj
    refine ⟨fun i i' h => ?_, ?_⟩
    · have : (i : ℕ) ≤ i' := h
      change (if (i' : ℕ) < j then (1 : ℤ) else 0) ≤ if (i : ℕ) < j then 1 else 0
      split_ifs <;> omega
    · rw [mu_fund]
      exact hev j hj
  have hneg : (-1 : Fin n → ℤ) ∈ M := by
    have anti : Antitone (1 : Fin n → ℤ) := fun _ _ _ => le_rfl
    have anti' : Antitone (-1 : Fin n → ℤ) := fun _ _ _ => le_rfl
    have hinv : (upow k n (1 : Fin n → ℤ))⁻¹ = upow k n (-1) := by
      rw [inv_eq_iff_mul_eq_one, ← upow_add]
      rw [upow, ← (diagT k (Fin n)).map_one]
      congr 1
      funext i
      simp
    have h1 : fund n n = (1 : Fin n → ℤ) := by
      funext i
      simp [fund]
    obtain ⟨-, e1⟩ := hfund n le_rfl
    rw [h1] at e1
    have u1 := (mulOp _ _ (upow_mem anti) (upow_mem anti)).2.2.2.2 (by rw [hinv]; exact upow_mem anti')
    have u2 := (mulOp _ _ (upow_mem anti') (upow_mem anti')).2.2.2.2 (by rw [← hinv, inv_inv]; exact upow_mem anti)
    refine ⟨anti', ?_⟩
    rw [u2]
    have hE : torusChar (mu ψ) (fun i => UpperTheory.V.Hi.unif k ^ (-1 : Fin n → ℤ) i) =
        (torusChar (mu ψ) (fun i => UpperTheory.V.Hi.unif k ^ (1 : Fin n → ℤ) i))⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← E_add]
      rw [neg_add_cancel]
      exact E_zero
    rw [hE, ← hinv]
    rw [u1] at e1
    have h3 : τ (upow k n 1)⁻¹ (τ (upow k n 1) v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [e1, map_smul] at h3
    rw [Units.val_inv_eq_inv_val, eq_inv_smul_iff₀ (Units.ne_zero _)]
    exact h3
  exact (antitone_mem M hfund hneg a ha).2
end LocEigAux
theorem UpperTheory.V.Z.Sym.Al.exists_fixd_dc_eq_expo_smul_of_equiv_prinSeries :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (W : Sig.Lev k) (ψ : Fin n → kˣ →* ℂˣ), (∀ i, IsSmoothChar (ψ i)) → (∀ i, ∀ u ∈ W.H, ψ i u = 1) →
        ∀ (T : Type) [AddCommGroup T] [Module ℂ T] (τ : Representation ℂ (GL (Fin n) k) T), Nonempty (τ.Equiv (prinSeries ψ)) →
        ∃ v : T, v ≠ 0 ∧ v ∈ Hi.fixd τ (W.J n) ∧ ∀ d, Sig.SDom d → Hi.dc τ (W.J n) (W.J n) (Sig.dg d) v = expo ψ d • v := by
  intro hLit k _ _ _ _ n W ψ _ hH T _ _ τ he
  have hE : Nonempty (τ.Equiv (Hi.PS (omg ψ))) := by
    show Nonempty (τ.Equiv (prinSeries fun i => omg ψ i * absPow k (((n : ℂ) - 1) / 2)))
    rw [om_shift]
    exact he
  have hHv : ∀ y ∈ W.H, valuation k (y : k) = 1 := fun y hy => W.H_le hy
  obtain ⟨v, hv, hv0, hev⟩ := _root_.UpperTheory.V.Hi.exists_ne_zero_mem_eig_uOp_eq_psEig_smul_of_equiv_ps hLit k n T τ (omg ψ) hE W.c
    (fun i y hy => by rw [om_unit ψ i (hHv y (W.le hy)), hH i y (W.le hy)]) (phi (omg ψ)) (phi_inv _)
  have hT : ∀ (u : Fin n → kˣ) (hu : u ∈ torusO k (Fin n)), τ (diagT k (Fin n) u) v = ((torusChar (mu ψ) u : ℂˣ) : ℂ) • v := by
    intro u hu
    have h1 := hv.2.2 ⟨diagT k (Fin n) u, u, hu, rfl⟩
    rw [phi_diag _ u hu, inv_inv] at h1
    have h2 : torusChar (omg ψ) u = torusChar (mu ψ) u := by
      rw [torusChar_apply, torusChar_apply]
      exact Finset.prod_congr rfl fun i _ => by rw [om_unit ψ i (hu i), mu_unit ψ i (hu i)]
    rw [← h2]
    exact h1
  have hvJ : v ∈ Hi.fixd τ (W.J n) := by
    let S : Subgroup (GL (Fin n) k) :=
      { carrier := {g | τ g v = v}
        mul_mem' := fun {a b} ha hb => by
          show τ (a * b) v = v
          rw [map_mul, Module.End.mul_apply, hb, ha]
        one_mem' := by
          show τ 1 v = v
          simp
        inv_mem' := fun {a} ha => by
          show τ a⁻¹ v = v
          conv_lhs => rw [← ha]
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
    have hle : W.J n ≤ S := by
      refine sup_le (sup_le (fun g hg => hv.1 g hg) ?_) fun g hg => hv.2.1 g hg
      rintro _ ⟨s, hs, rfl⟩
      have hs' : ∀ i, s i ∈ W.H := fun i => hs i trivial
      show τ (diagT k (Fin n) s) v = v
      rw [hT s fun i => hHv _ (hs' i), torusChar_apply]
      have : ∏ i, mu ψ i (s i) = 1 := Finset.prod_eq_one fun i _ => by
        rw [mu_unit ψ i (hHv _ (hs' i)), hH i _ (hs' i)]
      rw [this, Units.val_one, one_smul]
    exact fun g hg => hle hg
  refine ⟨v, hv0, hvJ, fun d hd => ?_⟩
  have hDd : UpperTheory.V.AlgebraTools.Dom d := fun i j hij => by
    rcases hij.eq_or_lt with rfl | h
    · exact le_rfl
    · exact (hd i j h).le
  let a : Fin n → ℤ := fun i => GlobalTheory.SmGL.ord k (d i)
  have ha : Antitone a := fun i j hij => by
    have := hDd i j hij
    rw [Sig.val_ord, Sig.val_ord] at this
    exact (zpow_le_zpow_iff_right_of_lt_one₀ Hi.GlAx.unif_pos uniformizer_lt_one).1 this
  let p : Fin n → kˣ := fun i => Hi.unif k ^ a i
  let u : Fin n → kˣ := d / p
  have hu : u ∈ torusO k (Fin n) := fun i => Hi.GlAx.val_div_ord (d i)
  have hdu : d = u * p := by simp [u]
  have hDu : UpperTheory.V.AlgebraTools.Dom u := fun i j _ => by rw [hu i, hu j]
  have hDp : UpperTheory.V.AlgebraTools.Dom p := fun i j hij => by
    have e : ∀ i, valuation k (p i : k) = valuation k (d i : k) := fun i => by
      rw [hdu, Pi.mul_apply, Units.val_mul, map_mul, hu i, one_mul]
    rw [e, e]
    exact hDd i j hij
  have hI := ((Sig.finFacts k W).2.2.2.2.2 n).1 (Sig.dg d)
  have h0 := (UpperTheory.V.AlgebraTools.hkApply ℂ _ T τ (W.J n) (W.J n) (Sig.dg d) hI).1 ⟨v, hvJ⟩
  have hm := (Sig.hkMul k W n T τ).1 u p hDu hDp
  let X : Hi.fixd τ (W.J n) := ⟨v, hvJ⟩
  have h1 := (Sig.hkMul k W n T τ).2 p hDp X
  have h2 := (Sig.hkMul k W n T τ).2 u hDu X
  have hp : (Hi.glIwa k n).uOp τ (Sig.dg p) v = ((torusChar (mu ψ) p : ℂˣ) : ℂ) • v := uOp_upow τ ψ hv.1 hev a ha
  have hu' : (Hi.glIwa k n).uOp τ (Sig.dg u) v = ((torusChar (mu ψ) u : ℂˣ) : ℂ) • v :=
    u_operator_torus_eigen (Hi.glIwa k n) τ (t := diagT k (Fin n) u) ⟨u, hu, rfl⟩ hv.1 (hT u hu)
  have e1 : UpperTheory.V.AlgebraTools.hk τ (W.J n) (Sig.dg p) X = ((torusChar (mu ψ) p : ℂˣ) : ℂ) • X := Subtype.ext (h1.trans hp)
  have h0' : Hi.dc τ (W.J n) (W.J n) (Sig.dg d) v = (UpperTheory.V.AlgebraTools.hk τ (W.J n) (Sig.dg (u * p)) X : T) := by
    rw [← hdu]
    exact h0.symm
  have hc : torusChar (mu ψ) d = torusChar (mu ψ) u * torusChar (mu ψ) p := by
    rw [← map_mul, ← hdu]
  rw [h0', ← hm, Module.End.mul_apply, e1, map_smul]
  show ((torusChar (mu ψ) p : ℂˣ) : ℂ) • (UpperTheory.V.AlgebraTools.hk τ (W.J n) (Sig.dg u) X : T) = _
  rw [h2]
  show ((torusChar (mu ψ) p : ℂˣ) : ℂ) • (Hi.glIwa k n).uOp τ (Sig.dg u) v = _
  rw [hu', smul_smul, expo_eq, hc, Units.val_mul, mul_comm]
end
