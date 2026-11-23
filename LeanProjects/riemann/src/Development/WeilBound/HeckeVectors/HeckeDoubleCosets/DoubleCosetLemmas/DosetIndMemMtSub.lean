import Development.WeilBound.HeckeVectors.HeckeDoubleCosets.DoubleCosetLemmas.MatchB
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SatakeDeterminesSphericalHeckeCharacterGL
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SatakeVectorIffInverseDoubleCosetsStatement

noncomputable section

namespace CompanionTheory.D.Upq.DoubleCosetLemmas.Mch

open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.PRep GlobalTheory.LFun GlobalTheory.LGrp GlobalTheory.WeylGL
open GlobalTheory.LFun.SatCompare GlobalTheory.CompanionTheory.Ipf.Val
open GlobalTheory.SplitHecke (IntM GInt Hk Reps tr yw nKer)

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}

local notation "𝒪" => HeightOneSpectrum.adicCompletionIntegers K v

theorem heckeVec_central {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {J : Subgroup G}
    {ρ : Representation ℂ G V} {x : V} (hx : x ∈ fixed ρ J) {z : G} (hz : ∀ g, z * g = g * z) :
    heckeVec ρ J (dosetInd ℂ J z) x = ρ z x := by
  rw [heckeVec_dosetInd hx (R := {z}) (by
    intro γ hγ
    rw [Finset.mem_singleton.1 hγ]
    exact mem_doset.2 ⟨1, one_mem _, 1, one_mem _, by simp⟩) (by
    intro g hg
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_doset.1 hg
    refine ⟨z, ⟨Finset.mem_singleton_self _, ?_⟩, fun γ hγ => Finset.mem_singleton.1 hγ.1⟩
    rw [← hz a, show z⁻¹ * (z * a * b) = a * b by group]
    exact mul_mem ha hb), Finset.sum_singleton]

theorem satEig_top (q n : ℕ) {B : Multiset ℂˣ} (hB : B.card = n) :
    satEig q n B n = ((B.prod : ℂˣ) : ℂ) := by
  have hp := Multiset.powersetCard_self (B.map fun b : ℂˣ => (b : ℂ))
  rw [Multiset.card_map, hB] at hp
  simp only [satEig, Multiset.esymm, hp, sub_self, mul_zero, zero_div, Complex.cpow_zero, one_mul,
    Multiset.map_singleton, Multiset.sum_singleton]
  exact (map_multiset_prod (Units.coeHom ℂ) B).symm

theorem npowU_add (y z : ℂ) : npowU v (y + z) = npowU v y * npowU v z :=
  Units.ext (npow_add v y z)

theorem npowU_zero : npowU v 0 = 1 := Units.ext (Complex.cpow_zero _)

theorem prod_npowU (s : Finset ℕ) (f : ℕ → ℂ) :
    ∏ i ∈ s, npowU v (f i) = npowU v (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [npowU_zero]
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, npowU_add, ih]

theorem seg_prod (t : ℕ) : (seg v 1 t).prod = 1 := by
  have h : ∑ i ∈ Finset.range t, (((t : ℂ) - 1) / 2 - i) = 0 := by
    have : ∀ n : ℕ, ∑ i ∈ Finset.range n, (i : ℂ) = n * (n - 1) / 2 := fun n => by
      induction n with
      | zero => simp
      | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
    rw [Finset.sum_sub_distrib, this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  simp only [seg, one_mul]
  rw [← Finset.prod_eq_multiset_prod, prod_npowU, h, npowU_zero]

theorem seg_inv (t : ℕ) : (seg v 1 t).map (·⁻¹) = seg v 1 t := by
  simp only [seg, one_mul, Multiset.map_map, Function.comp_def]
  refine Multiset.map_eq_map_of_bij_of_nodup _ _ (Finset.range t).nodup (Finset.range t).nodup
    (fun i _ => t - 1 - i) (fun i hi => ?_) (fun i hi j hj e => ?_)
    (fun j hj => ⟨t - 1 - j, ?_, ?_⟩) fun i hi => ?_
  · have := Finset.mem_range.1 hi; exact Finset.mem_range.2 (by omega)
  · have := Finset.mem_range.1 hi; have := Finset.mem_range.1 hj; omega
  · have := Finset.mem_range.1 hj; exact Finset.mem_range.2 (by omega)
  · have := Finset.mem_range.1 hj; omega
  · have h : i + 1 ≤ t := Finset.mem_range.1 hi
    rw [inv_eq_iff_mul_eq_one, ← npowU_add, ← npowU_zero (v := v)]
    congr 1
    rw [Nat.sub_sub, Nat.cast_sub (by omega)]
    push_cast
    ring

theorem seg_card (t : ℕ) : (seg v 1 t).card = t := by simp [seg]

theorem acts_neg {m : ℕ} {ϖ : Cv v} (hu : IsUnifV K v ϖ) (h0 : ϖ ≠ 0) (B : Multiset ℂˣ) :
    Acts (dosetInd ℂ (KGL v m) (tor h0 fun _ => -1)) B ((B.prod⁻¹ : ℂˣ) : ℂ) := by
  intro V _ _ ρ x hx
  have h1 := hx.2.2.2 ϖ hu m le_rfl
  rw [Tj_eq h0, satEig_top _ _ hx.2.2.1] at h1
  simp only [Fin.is_lt, if_true] at h1
  rw [heckeVec_central hx.2.1 (tor_const_comm h0 1)] at h1
  rw [heckeVec_central hx.2.1 (tor_const_comm h0 (-1))]
  have h2 : tor h0 (fun _ : Fin m => -1) * tor h0 (fun _ => 1) = 1 := by
    rw [← tor_add]; ext1; simp [tor_val]
  have h3 := congrArg (ρ (tor h0 fun _ : Fin m => -1)) h1
  rw [← Module.End.mul_apply, ← map_mul, h2, map_one, Module.End.one_apply, map_smul] at h3
  conv_rhs => rw [h3, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]

theorem wt_const {m l : ℕ} {ϖ : Cv v} (h0 : ϖ ≠ 0) :
    wt ((l : ℝ) / 2) (tor h0 fun _ : Fin m => -1) = ((absV v ϖ⁻¹ ^ ((m * l : ℝ) / 2) : ℝ) : ℂ) := by
  rw [wt, tor_val, det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin, absV_pow,
    _root_.zpow_neg_one, ← Real.rpow_natCast, ← Real.rpow_mul (absV_nonneg _), mul_div_assoc]

theorem neg_mem_mtSub {c t : ℕ} {ϖ : Cv v} (hu : IsUnifV K v ϖ) (h0 : ϖ ≠ 0) :
    dosetInd ℂ (KGL v (c + t)) (tor h0 fun _ => -1) ∈ mtSub v c t := by
  refine ⟨dosetInd ℂ (KGL v c) (tor h0 fun _ => -1), Final.DosetIndMem _ _ ℂ _,
    Final.DosetIndMem _ _ ℂ _, ?_, fun B _ => ⟨_, acts_neg hu h0 B, ?_⟩⟩
  · rw [heckeVec_central (sphericalVector_fixed_left _ _) (tor_const_comm h0 (-1)),
      heckeVec_central (sphericalVector_fixed_right _ _) (tor_const_comm h0 (-1))]
    funext y
    rw [rT_apply, rS_apply, wt_const, wt_const, mul_comm (c : ℝ)]
    congr 2
    ext i j
    simp [tor_val, diagonal_mul, mul_diagonal, mul_comm]
  · have := acts_neg (m := c + t) hu h0 (B + seg v 1 t)
    rwa [Multiset.prod_add, seg_prod, mul_one] at this

theorem dosetInd_mem_mtSub {c t : ℕ} (g : GL (Fin (c + t)) (Cv v)) :
    dosetInd ℂ (KGL v (c + t)) g ∈ mtSub v c t := by
  have hK : IsCommensurated (KGL v (c + t)) := Final.GLintComm K v _
  obtain ⟨ϖ, hu⟩ := exists_isUnifV v
  have h0 := ne_zero_of_isUnifV hu
  have shift : ∀ g, dosetInd ℂ (KGL v (c + t)) g ∈ mtSub v c t →
      dosetInd ℂ (KGL v (c + t)) (tor h0 (fun _ => -1) * g) ∈ mtSub v c t := by
    intro g hg
    set z := tor h0 fun _ : Fin (c + t) => -1
    have hc := conv_mem_mtSub _ (neg_mem_mtSub hu h0) _ hg
    have hb := (Final.HeckeConvMem _ _ ℂ hK _ (Final.DosetIndMem _ (KGL v (c + t)) ℂ z) _
      (Final.DosetIndMem _ (KGL v (c + t)) ℂ g)).1
    have hne := conv_top hK z g
    have e : dosetInd ℂ (KGL v (c + t)) (z * g) = (conv (KGL v (c + t))
        (dosetInd ℂ (KGL v (c + t)) z)
        (dosetInd ℂ (KGL v (c + t)) g) (z * g))⁻¹ • conv (KGL v (c + t))
        (dosetInd ℂ (KGL v (c + t)) z) (dosetInd ℂ (KGL v (c + t)) g) := by
      funext x
      by_cases hx : ∃ a ∈ KGL v (c + t), ∃ b ∈ KGL v (c + t), x = a * (z * g) * b
      · rw [dosetInd_of_mem hx]
        obtain ⟨a, ha, b, hb', rfl⟩ := hx
        rw [Pi.smul_apply, hb ⟨a, ha⟩ ⟨b, hb'⟩, smul_eq_mul, inv_mul_cancel₀ hne]
      · rw [dosetInd_of_not hx, Pi.smul_apply, smul_eq_mul, eq_comm, mul_eq_zero]
        refine Or.inr (by_contra fun h => hx ?_)
        obtain ⟨y, y', ⟨a, ha, b, hb, rfl⟩, ⟨a', ha', b', hb', rfl⟩, rfl⟩ := conv_supp hK h
        refine ⟨a * b * a', mul_mem (mul_mem ha hb) ha', b', hb', ?_⟩
        have : z * (b * a') = b * a' * z := tor_const_comm h0 (-1) (b * a')
        calc a * z * b * (a' * g * b') = a * (z * (b * a')) * g * b' := by group
          _ = _ := by rw [this]; group
    rw [e]
    exact Submodule.smul_mem _ _ hc
  have hall : ∀ (N : ℕ) (a : Fin (c + t) → ℤ), Antitone a → (∀ i, 0 ≤ a i + N) →
      dosetInd ℂ (KGL v (c + t)) (tor h0 a) ∈ mtSub v c t := by
    intro N
    induction N with
    | zero =>
      intro a ha ha0
      obtain ⟨d, rfl⟩ : ∃ d : Fin (c + t) → ℕ, a = fun i => (d i : ℤ) :=
        ⟨fun i => (a i).toNat, funext fun i =>
          (Int.toNat_of_nonneg (by simpa using ha0 i)).symm⟩
      exact gen_nat h0 hu _ (Tj_mem_mtSub hu) conv_mem_mtSub _ _ d
        (fun a b hab => Int.ofNat_le.1 (ha hab)) rfl rfl
    | succ N ih =>
      intro a ha ha0
      have := shift _ (ih (fun i => a i + 1) (fun i j hij => by have := ha hij; simp only; omega)
        fun i => by have := ha0 i; push_cast at this; omega)
      rw [← tor_add] at this
      convert this using 3
      funext i
      simp
  obtain ⟨a, ha, hg⟩ := cartan h0 hu g
  rw [dosetInd_congr hg]
  refine hall (∑ i, (a i).natAbs) a ha fun i => ?_
  have := Finset.single_le_sum (f := fun i => (a i).natAbs) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ i)
  omega

def theta (m : ℕ) : GL (Fin m) (Cv v) ≃* GL (Fin m) (Cv v) where
  toFun g := tr g⁻¹
  invFun g := tr g⁻¹
  left_inv _ := Units.ext rfl
  right_inv _ := Units.ext rfl
  map_mul' g h := by rw [_root_.mul_inv_rev, GlobalTheory.SplitHecke.tr_mul]

theorem theta_theta {m : ℕ} (g : GL (Fin m) (Cv v)) : theta m (theta m g) = g := Units.ext rfl

theorem theta_mem {m : ℕ} (g : GL (Fin m) (Cv v)) : g ∈ KGL v m ↔ theta m g ∈ KGL v m := by
  rw [mem_KGL, mem_KGL]
  exact (GlobalTheory.SplitHecke.gInt_tr.trans GlobalTheory.SplitHecke.gInt_inv).symm

theorem theta_tor {m : ℕ} {ϖ : Cv v} (h0 : ϖ ≠ 0) (a : Fin m → ℤ) :
    theta m (tor h0 a) = (tor h0 a)⁻¹ := Units.ext (diagonal_transpose _)

theorem dosetInd_theta {m : ℕ} (g : GL (Fin m) (Cv v)) :
    dosetInd ℂ (KGL v m) g ∘ theta m = dosetInd ℂ (KGL v m) (theta m g) := by
  funext x
  by_cases h : ∃ a ∈ KGL v m, ∃ b ∈ KGL v m, x = a * theta m g * b
  · rw [dosetInd_of_mem h]
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    exact dosetInd_of_mem ⟨_, (theta_mem a).1 ha, _, (theta_mem b).1 hb, by
      rw [map_mul, map_mul, theta_theta]⟩
  · rw [dosetInd_of_not h]
    refine dosetInd_of_not fun ⟨a, ha, b, hb, e⟩ => h ⟨_, (theta_mem a).1 ha, _,
      (theta_mem b).1 hb, ?_⟩
    rw [← map_mul, ← map_mul, ← e, theta_theta]

theorem heckeVec_theta {m : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (GL (Fin m) (Cv v)) V} {x : V} (hx : x ∈ fixed ρ (KGL v m))
    (g : GL (Fin m) (Cv v)) :
    heckeVec (ρ.comp (theta m).symm.toMonoidHom) (KGL v m) (dosetInd ℂ (KGL v m) g) x =
      heckeVec ρ (KGL v m) (dosetInd ℂ (KGL v m) (theta m g)) x := by
  rw [heckeVec_comp_symm (theta m) theta_mem (Final.DosetIndMem _ (KGL v m) ℂ g).1 hx,
    dosetInd_theta]

theorem dosetInd_inv {G : Type} [Group G] (J : Subgroup G) (g : G) :
    (fun x => dosetInd ℂ J g x⁻¹) = dosetInd ℂ J g⁻¹ := by
  funext x
  by_cases h : ∃ a ∈ J, ∃ b ∈ J, x = a * g⁻¹ * b
  · rw [dosetInd_of_mem h]
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    exact dosetInd_of_mem ⟨_, inv_mem hb, _, inv_mem ha, by group⟩
  · rw [dosetInd_of_not h]
    refine dosetInd_of_not fun ⟨a, ha, b, hb, e⟩ => h ⟨_, inv_mem hb, _, inv_mem ha, ?_⟩
    rw [← inv_inv x, e]; group

theorem sat_theta {m : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (GL (Fin m) (Cv v)) V} {x : V} {B : Multiset ℂˣ}
    (hx : IsSatVecGL v ρ x B) :
    IsSatVecGL v (ρ.comp (theta m).symm.toMonoidHom) x (B.map (·⁻¹)) := by
  refine ⟨hx.1, (mem_fixed_comp_symm (theta m) theta_mem).2 hx.2.1, by simpa using hx.2.2.1,
    fun ϖ hu j hj => ?_⟩
  have h0 := ne_zero_of_isUnifV hu
  have := (GlobalTheory.T.satake_vector_iff_inverse_doubleCosets K v m V ρ x B hx.1 hx.2.1 hx.2.2.1).1 hx ϖ hu j hj
  rw [Tj_eq h0, dosetInd_inv] at this
  rw [Tj_eq h0, heckeVec_theta hx.2.1, theta_tor, this]

theorem exists_sat (m : ℕ) (B : Multiset ℂˣ) (hB : B.card = m) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V)
      (ρ : Representation ℂ (GL (Fin m) (Cv v)) V) (x : V), IsSatVecGL v ρ x B := by
  obtain ⟨α, rfl⟩ : ∃ α : Fin m → ℂˣ, Finset.univ.val.map α = B := by
    obtain ⟨l, rfl⟩ := Quot.exists_rep B
    obtain rfl : l.length = m := hB
    exact ⟨l.get, by rw [Fin.univ_val_map, List.ofFn_get]; rfl⟩
  obtain ⟨x, hx⟩ := (hasSatGL_psFunGL (w := v) α).exists_vec
  exact ⟨_, _, _, _, x, hx⟩

theorem hecke_eq_sum {m : ℕ} {ϖ : Cv v} (hu : IsUnifV K v ϖ) (h0 : ϖ ≠ 0)
    {f : GL (Fin m) (Cv v) → ℂ} (hf : f ∈ Hecke ℂ (KGL v m)) :
    ∃ (I : Finset (Fin m → ℤ)) (a : (Fin m → ℤ) → ℂ),
      f = ∑ e ∈ I, a e • dosetInd ℂ (KGL v m) (tor h0 e) := by
  have : f ∈ Submodule.span ℂ (Set.range fun e : Fin m → ℤ => dosetInd ℂ (KGL v m) (tor h0 e)) :=
    mem_of_supp _ hf fun g _ => by
      obtain ⟨a, -, hg⟩ := cartan h0 hu g
      rw [dosetInd_congr hg]
      exact Submodule.subset_span ⟨a, rfl⟩
  obtain ⟨a, ha⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 this
  exact ⟨a.support, a, ha.symm⟩

theorem linAct_S {n c : ℕ} (g : GL (Fin c) (Cv v)) (Φ) (y) :
    linAct v 1 1 g (1 : GL (Fin n) (Cv v)) Φ y = rS v n c g Φ y := by
  simp [linAct, rS_apply, wt, absV_one]

theorem linAct_alt {n c : ℕ} (z : GL (Fin n) (Cv v)) (Φ) (y) :
    linAct v 1 1 (1 : GL (Fin c) (Cv v)) z Φ y = rT v n c ((theta n).symm z) Φ y := by
  have h : ((theta n).symm z).1.det = z.1.det⁻¹ := by
    change ((z⁻¹).1ᵀ).det = _
    rw [det_transpose, Matrix.coe_units_inv, det_nonsing_inv, Ring.inverse_eq_inv']
  have h2 : ((theta n).symm z).1ᵀ = (z⁻¹).1 := rfl
  rw [rT_apply, wt, h, h2, absV_inv, Real.inv_rpow (absV_nonneg _), ← Real.rpow_neg (absV_nonneg _),
    ← neg_div]
  simp [linAct, absV_one]

theorem sphMatchAll : SphMatchAll := by
  intro K _ _ v c t ϖ hu m'
  have h0 := ne_zero_of_isUnifV hu
  have hK : IsCommensurated (KGL v c) := Final.GLintComm K v _
  have hK' : IsCommensurated (KGL v (c + t)) := Final.GLintComm K v _
  have hd := fun {m} (g : GL (Fin m) (Cv v)) => Final.DosetIndMem _ (KGL v m) ℂ g
  obtain ⟨f, -, a2, a3, a4⟩ := dosetInd_mem_mtSub (theta (c + t) m')
  obtain ⟨I, a, rfl⟩ := hecke_eq_sum hu h0 a2
  refine ⟨I, a, tor h0, fun e => rfl, fun y => ?_, fun B lam hlam => ?_⟩
  · rw [← heckeVec_theta (sphericalVector_fixed_left _ _), heckeVec_sum_left hK _ _ _ _ fun e => hd _] at a3
    have := congrFun a3 y
    rw [heckeVec_apply hK' (hd _), Finset.sum_apply] at this
    simp only [linAct_S, linAct_alt]
    refine this.trans (Finset.sum_congr rfl fun e _ => ?_)
    rw [Pi.smul_apply, smul_eq_mul, heckeVec_apply hK (hd _)]
    rfl
  · obtain ⟨V, _, _, ρ, x, hx, -⟩ := hlam 0
    have hB := hx.2.2.1
    obtain ⟨l, l1, l2⟩ := a4 (B.map (·⁻¹)) (by simpa using hB)
    obtain ⟨V', _, _, ρ', x', hx'⟩ := exists_sat (v := v) (c + t) (B + seg v 1 t)
      (by rw [Multiset.card_add, hB, seg_card])
    have e1 := l1 V _ x (sat_theta hx)
    have e2 := l2 V' _ x' (by simpa only [Multiset.map_add, seg_inv] using sat_theta hx')
    rw [heckeVec_theta hx'.2.1, theta_theta] at e2
    have e3 : ∀ e, heckeVec (ρ.comp (theta c).symm.toMonoidHom) (KGL v c)
        (dosetInd ℂ (KGL v c) (tor h0 e)) x = lam e • x := fun e => by
      obtain ⟨V₀, _, _, ρ₀, x₀, hx₀, e₀⟩ := hlam e
      obtain ⟨z, hz⟩ := GlobalTheory.ChainOnto.SatHeckeChar.heckeVec_eq_smul_of_isSatVecGL K v c B _
        (hd (tor h0 e)⁻¹)
      rw [heckeVec_theta hx.2.1, theta_tor, hz V ρ x hx,
        smul_left_injective ℂ hx₀.1 ((hz V₀ ρ₀ x₀ hx₀).symm.trans e₀)]
    rw [heckeVec_sum_left hK _ _ _ _ fun e => hd _] at e1
    simp only [e3, smul_smul, ← Finset.sum_smul] at e1
    refine ⟨V', _, _, ρ', x', hx', ?_⟩
    rw [e2, smul_left_injective ℂ hx.1 e1]

end CompanionTheory.D.Upq.DoubleCosetLemmas.Mch

end
