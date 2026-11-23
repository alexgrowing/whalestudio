import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefTwistPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOneOfFiniteOrderAny
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionValueAtTorsionPointEqSumTerms
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueThetaConst
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SumIOfFinite
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsExpandsFScale
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaTableAlgClosedCompleteSingleValued

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section
namespace GlobalTheory.Poinc.Tors.ValPair

section Sums
open GlobalTheory.AdicSum

theorem sumI_finset {R : Type} [CommRing R] {I : Ideal R} {E Ix κ : Type} [AddCommGroup E] [Module R E]
    (S : Finset κ) (x : κ → Ix → E) (s : κ → E) (h : ∀ j, SumI I (x j) (s j)) :
    SumI I (fun i => ∑ j ∈ S, x j i) (∑ j ∈ S, s j) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨⊥, Submodule.fg_bot, by simp, by simp, fun n => ⟨∅, by simp⟩⟩
  | insert j S hj ih => simpa only [Finset.sum_insert hj] using sumI_add (h j) ih

theorem sumI_conv {R : Type} [CommRing R] [IsNoetherianRing R] {I : Ideal R} (hI : I ≤ Ideal.jacobson ⊥)
    {F X : Type} [CommRing F] [Algebra R F] [AddCommGroup X] {a b c : X → F} {r r' r'' : F}
    (ha : SumI I a r) (hb : SumI I b r') (hc : ∀ α, SumI I (fun χ => a χ * b (α - χ)) (c α)) (h : SumI I c r'') :
    r'' = r * r' := by
  classical
  have hb' := hb
  obtain ⟨N, hN, hr, hx, hS⟩ := ha
  obtain ⟨N', hN', hr', hx', -⟩ := hb'
  have key : ∀ n : ℕ, r'' - r * r' ∈ I ^ n • (N * N') := by
    intro n
    obtain ⟨S, hS⟩ := hS n
    have hm : ∀ u ∈ I ^ n • N, ∀ v ∈ N', u * v ∈ I ^ n • (N * N') := fun u hu v hv => by
      rw [← smul_mul_assoc]
      exact Submodule.mul_mem_mul hu hv
    let π := (I ^ n • (N * N')).mkQ
    have h0 : ∀ α χ, χ ∉ S → π (a χ * b (α - χ)) = 0 := fun α χ hχ => by
      refine (Submodule.Quotient.mk_eq_zero _).2 (hm _ ?_ _ (hx' _))
      have := sub_mem (hS S le_rfl) (hS (insert χ S) (Finset.subset_insert _ _))
      rwa [Finset.sum_insert hχ, sub_sub_sub_cancel_left, add_sub_cancel_right] at this
    have h1 : ∀ α, π (c α) = ∑ χ ∈ S, π (a χ * b (α - χ)) := fun α =>
      sumI_unique hI (sumI_map π (hc α)) (sumI_of_finite I _ S (h0 α))
    have h2 : ∀ χ, SumI I (fun α => π (a χ * b (α - χ))) (π (a χ * r')) := fun χ =>
      sumI_map π (sumI_map (LinearMap.mulLeft R (a χ)) ((sumI_comp_iff (e := fun α => α - χ) sub_left_injective
        fun β hβ => absurd ⟨β + χ, add_sub_cancel_right _ _⟩ hβ).2 hb))
    have h3 := sumI_finset S _ _ h2
    simp only [← h1] at h3
    have h4 := sumI_unique hI (sumI_map π h) h3
    rw [← map_sum, ← Finset.sum_mul] at h4
    have h5 := sub_mem ((Submodule.Quotient.eq _).1 h4) (hm _ (hS S le_rfl) _ hr')
    convert h5 using 1
    ring
  have e : SumI I (fun _ : Empty => (0 : F)) (r'' - r * r') :=
    ⟨N * N', hN.mul hN', by simpa using key 0, fun i => i.elim, fun n => ⟨∅, fun T _ => by simpa using key n⟩⟩
  exact sub_eq_zero.1 (sumI_unique hI e (by simpa using sumI_of_finite I (fun _ : Empty => (0 : F)) ∅ fun _ _ => rfl))

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem sumF_conv (hI : AdmBase R I) {X : Type} [AddCommGroup X] {a b c : X → F} {r r' r'' : F}
    (ha : SumF I F a r) (hb : SumF I F b r') (hc : ∀ α, SumF I F (fun χ => a χ * b (α - χ)) (c α))
    (h : SumF I F c r'') : r'' = r * r' := by
  obtain ⟨hN, -, -, hc'⟩ := hI
  letI : Module R F := Module.compHom F (algebraMap R (FractionRing R))
  letI : Algebra R F := Algebra.ofModule (fun q x y => smul_mul_assoc (algebraMap R (FractionRing R) q) x y)
    (fun q x y => mul_smul_comm (algebraMap R (FractionRing R) q) x y)
  exact sumI_conv (IsAdicComplete.le_jacobson_bot I) ha hb hc h

theorem sumF_smul (hI : AdmBase R I) {Ix : Type} {x : Ix → F} {s : F} (c : F) (h : SumF I F x s) :
    SumF I F (fun i => c * x i) (c * s) := by
  simpa only [add_zero] using (sumF_calculus R I hI F _ _ _ _ _).2.1 h (ProdConv.sumF_zero (I := I) (F := F)) c

theorem exists_degree_constant (hI : AdmBase R I) {X : Type} [AddCommGroup X] (Rel : ℕ → (X → F) → F → Prop) (n : ℕ)
    (hn : 1 ≤ n) (hsum : ∀ k a c, 1 ≤ k → Rel k a c → ∃ r, SumF I F a r)
    (hmul : ∀ k k' a a' c c', 1 ≤ k → 1 ≤ k' → Rel k a c → Rel k' a' c' →
      ∃ a'', Rel (k + k') a'' (c * c') ∧ ∀ α, SumF I F (fun χ => a χ * a' (α - χ)) (a'' α))
    (hex : ∀ k, 4 ≤ k → ∃ a c, Rel k a c ∧ c ≠ 0)
    (hlev : ∀ m, 1 ≤ m → ∃ κ : F, κ ≠ 0 ∧ ∀ a c, Rel (n * m) a c → SumF I F a (κ * c)) :
    ∃ l : F, l ≠ 0 ∧ ∀ k a c, 1 ≤ k → Rel k a c → SumF I F a (l ^ k * c) := by
  have uniq : ∀ {a : X → F} {s s'}, SumF I F a s → SumF I F a s' → s = s' := fun h h' =>
    (sumF_calculus R I hI F _ _ (fun _ => 0) _ _).1 h h'
  have hcompl : ∀ k, ∃ k', 4 ≤ k' ∧ ∃ κ : F, κ ≠ 0 ∧ ∀ a c, Rel (k + k') a c → SumF I F a (κ * c) := fun k => by
    obtain ⟨k', e, h4⟩ : ∃ k', n * (k + 4) = k + k' ∧ 4 ≤ k' := by
      have : k + 4 ≤ n * (k + 4) := Nat.le_mul_of_pos_left _ hn
      exact ⟨n * (k + 4) - k, by omega, by omega⟩
    exact ⟨k', h4, e ▸ hlev (k + 4) (by omega)⟩
  have hne : ∀ k a c r, 1 ≤ k → Rel k a c → c ≠ 0 → SumF I F a r → r ≠ 0 := by
    intro k a c r hk ha hc hr h0
    obtain ⟨k', h4, κ, hκ, H⟩ := hcompl k
    obtain ⟨a', c', h', hc'⟩ := hex k' h4
    obtain ⟨r', hr'⟩ := hsum k' a' c' (by omega) h'
    obtain ⟨a'', h₁, h₂⟩ := hmul _ _ _ _ _ _ hk (by omega) ha h'
    have := sumF_conv hI hr hr' h₂ (H _ _ h₁)
    rw [h0, zero_mul] at this
    exact mul_ne_zero hκ (mul_ne_zero hc hc') this
  have hmu : ∀ k, 1 ≤ k → ∃ mu : F, mu ≠ 0 ∧ ∀ a c, Rel k a c → SumF I F a (mu * c) := by
    intro k hk
    obtain ⟨k', h4, κ, hκ, H⟩ := hcompl k
    obtain ⟨a', c', h', hc'⟩ := hex k' h4
    obtain ⟨r', hr'⟩ := hsum k' a' c' (by omega) h'
    have h0 := hne k' a' c' r' (by omega) h' hc' hr'
    refine ⟨κ * c' / r', div_ne_zero (mul_ne_zero hκ hc') h0, fun a c ha => ?_⟩
    obtain ⟨r, hr⟩ := hsum k a c hk ha
    obtain ⟨a'', h₁, h₂⟩ := hmul _ _ _ _ _ _ hk (by omega) ha h'
    have := sumF_conv hI hr hr' h₂ (H _ _ h₁)
    rwa [show κ * c' / r' * c = r by field_simp; linear_combination this]
  choose! mu hmu0 hmu using hmu
  have hq : ∀ k k', 1 ≤ k → 4 ≤ k' → ∀ a c, Rel k a c → SumF I F a (mu (k + k') / mu k' * c) := by
    intro k k' hk hk' a c ha
    obtain ⟨a', c', h', hc'⟩ := hex k' hk'
    obtain ⟨a'', h₁, h₂⟩ := hmul _ _ _ _ _ _ hk (by omega) ha h'
    have h0 := hmu0 k' (by omega)
    have := sumF_conv hI (hmu k hk _ _ ha) (hmu k' (by omega) _ _ h') h₂ (hmu _ (by omega) _ _ h₁)
    have e : mu (k + k') * c = mu k * c * mu k' := mul_right_cancel₀ hc' (by linear_combination this)
    rw [show mu (k + k') / mu k' * c = mu k * c by field_simp; linear_combination e]
    exact hmu k hk _ _ ha
  have hm : ∀ k k', 4 ≤ k → 4 ≤ k' → mu (k + k') = mu k * mu k' := by
    intro k k' hk hk'
    obtain ⟨a, c, h, hc⟩ := hex k hk
    have e := mul_right_cancel₀ hc (uniq (hq k k' (by omega) hk' a c h) (hmu k (by omega) a c h))
    exact (div_eq_iff (hmu0 k' (by omega))).1 e
  have h40 := hmu0 4 (by omega)
  have h50 := hmu0 5 (by omega)
  have h20 : mu 5 ^ 4 = mu 4 ^ 5 := by
    have a₁ : mu 8 = _ := hm 4 4 le_rfl le_rfl
    have a₂ : mu 16 = _ := hm 8 8 (by omega) (by omega)
    have a₃ : mu 20 = _ := hm 16 4 (by omega) le_rfl
    have b₁ : mu 10 = _ := hm 5 5 (by omega) (by omega)
    have b₂ : mu 20 = _ := hm 10 10 (by omega) (by omega)
    rw [b₁] at b₂
    rw [a₂, a₁, b₂] at a₃
    linear_combination a₃
  have hp : ∀ k, mu (k + 4) = (mu 5 / mu 4) ^ (k + 4) := by
    intro k
    induction k with
    | zero => rw [zero_add, div_pow, h20]; field_simp
    | succ k ih =>
      have a₁ : mu (k + 1 + 4 + 4) = _ := hm (k + 1 + 4) 4 (by omega) le_rfl
      have a₂ : mu (k + 1 + 4 + 4) = _ := hm (k + 4) 5 (by omega) (by omega)
      rw [show k + 1 + 4 = k + 4 + 1 from rfl, pow_succ, ← ih, mul_div_assoc', eq_div_iff h40]
      exact a₁.symm.trans a₂
  refine ⟨mu 5 / mu 4, div_ne_zero h50 h40, fun k a c hk ha => ?_⟩
  have := hq k 4 hk le_rfl a c ha
  have h4 : mu 4 = (mu 5 / mu 4) ^ 4 := hp 0
  rwa [hp k, pow_add, ← h4, mul_div_cancel_right₀ _ h40] at this

end Sums

section Unif
open GlobalTheory.UT.CoefBasic GlobalTheory.AdicSum
variable {R : Type} [CommRing R] [IsDomain R] [CharZero R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  {F : Type} [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F]

theorem value_at_level (hB : AdmBase R I) (hG : IsSemiAbelian G) (U : Unif I D A G)
    {w₀ ρ} (hN : NormW U.toUnifPre w₀ ρ) {N : ℕ} (hN1 : 1 ≤ N) (q : QkPt D.toPre F N) (x : TFK (R := R) F ⟶ A.A)
    (hx : QkToAkU U.toUnifPre F N q x) (e : FrAt x) (he : e.IsGen) (w : Frm D.toPre F N q.g.b) (hw : w.IsGen) :
    ∃ κ : F, κ ≠ 0 ∧ ∀ (t : SecA A F N) s (c : F), U.ExpandsF F N w₀ t s → ValAt t x e c →
      SumF I F (coef s q.g w) (κ * c) := by
  have hL := GlobalTheory.firstFiveLaws
  haveI : Subsingleton (TFK (R := R) F).left := inferInstanceAs (Subsingleton (Spec (CommRingCat.of F)))
  haveI : Nonempty (TFK (R := R) F).left := inferInstanceAs (Nonempty (Spec (CommRingCat.of F)))
  obtain ⟨hxN, hθ⟩ := hx w₀ hN.1
  obtain ⟨θ, rfl⟩ := GlobalTheory.BoxTheta.exists_theta hL.1.kerPow A hN1 (T := TFK (R := R) F) x hxN
  obtain ⟨w', hw', hΦ⟩ := hθ θ rfl
  obtain ⟨u, hu, hval⟩ := EvalLevel.exists_act_value hN.2.1 N θ e he
  obtain ⟨o, ho⟩ := exists_zero_gt (D := D.toPre) (F := F)
  obtain ⟨w₁, hw₁⟩ := (coef_basic R D.toPre F N o).2.1 ho.1
  have hadd : o.IsAdd q.g q.g := by
    rw [GlobalTheory.TorusExt.isZero_unique ho GlobalTheory.TorusExt.isZero_gtZero]
    have := GlobalTheory.TorusExt.isAdd_gtAdd (GlobalTheory.TorusExt.gtZero D.toPre F) q.g
    rwa [GlobalTheory.TorusExt.gtZero_add] at this
  obtain ⟨ω, hω, -, hc⟩ := GlobalTheory.TorsionAnyChar.coefPhi_any hL R _ hB D F N hN1 q w' hw' o q.g hadd w₁ hw₁.1
  obtain ⟨d, hd, -, hdc⟩ := ((coef_basic R D.toPre F N q.g).2.2 ω hω).2.2.1 w hw
  refine ⟨d * u, mul_ne_zero hd hu, fun t s c hts hc' => ?_⟩
  obtain ⟨t', ht'⟩ := GlobalTheory.VVRank.exists_isTwistPull A.A (ψ := translT A.A θ.pt) (m := translPt A.A θ.pt)
    (hm := lift_snd _ _) (a := N) (b := N) (α := θ.φ) A.isLB θ.isGen t
  obtain ⟨s', hs', -⟩ := ((GlobalTheory.TorsionAnyChar.expBijF_any hL R _ hB D A G hG U).1 F N hN1 w₀ hN.1).1 t'
  have h₁ := (sumF_origin hL R _ hB D A G hG U F).2.2 w₀ ρ hN N t' s' hs' o w₁ ho hw₁ (u * c)
    (hval t t' c ht' hc')
  have h₂ := ((sumF_calculus R I hB F _ _ (fun _ => 0) _ 0).2.2 _ (fun β => β + q.y) (add_left_injective _)
    fun β hβ => absurd ⟨β - q.y, sub_add_cancel _ _⟩ hβ).2 h₁
  have h₃ := hc 1 N le_rfl (Nat.mul_one N).symm q (one_nsmul _).symm rfl w' w₁ ω ⟨hw', fun _ _ _ => (pow_one _).symm⟩
    ⟨hw₁.1, fun _ _ _ => (pow_one _).symm⟩ ⟨hω, fun _ _ _ => (pow_one _).symm⟩ s s' (hΦ t t' s s' hts hs' ht')
  have h₄ := sumF_smul hB d h₂
  simp only [Function.comp_apply, h₃, ← hdc] at h₄
  rw [_root_.mul_assoc]
  exact h₄

attribute [local instance] TorusExt.gtGroup in

theorem exists_sumF (hB : AdmBase R I) (hG : IsSemiAbelian G) (U : Unif I D A G)
    {w₀ ρ} (hN : NormW U.toUnifPre w₀ ρ) {n : ℕ} (hn : 1 ≤ n) (p : QkPt D.toPre F n) (hp : p.y = 0) {k : ℕ}
    (hk : 1 ≤ k) (W : Frm D.toPre F k p.g.b) (hW : W.IsGen) (t : SecA A F k) (s : Fam D.toPre F k)
    (hs : U.ExpandsF F k w₀ t s) : ∃ r, SumF I F (coef s p.g W) r := by
  have hL := GlobalTheory.firstFiveLaws
  have hpos : 1 ≤ k * n ^ 2 := Nat.mul_pos hk (Nat.pow_pos hn)
  obtain ⟨h, hh⟩ := (GlobalTheory.TorsionAnyChar.gtOnto_any hL R I hB D F).2.1 n hn p.g
  let q : QkPt D.toPre F (k * n ^ 2) := TorusExt.qkMk D.tau_bimult 0 h (by
    rw [show k * n ^ 2 = n * n * k by ring, mul_nsmul, mul_nsmul, ← (TorusExt.isNsmul_iff_eq _ _ _).1 hh,
      TorusExt.qk_nsmul D.tau_bimult p, hp, map_zero, smul_zero])
  obtain ⟨x, hx⟩ := GlobalTheory.TorsionAnyChar.existsTransl_any hL R I hB D A G hG U F _ hpos q
  have hx' := (GlobalTheory.TorsionAnyChar.indAtTransl_any hL R I hB D A G hG U F _ hpos q x).1
    (hx 1 _ le_rfl (Nat.mul_one _).symm q (one_nsmul _).symm rfl)
  obtain ⟨E, eG, eA, eB, eh, eAct⟩ := (GlobalTheory.IntEnd.exists_nsmul_and_neg hL R _ hB D A G hG U).1 n
  have hinj : Function.Injective E.h := fun a b h => by
    rw [eh, eh, ← natCast_zsmul, ← natCast_zsmul] at h
    exact smul_right_injective _ (by exact_mod_cast (by omega : n ≠ 0)) h
  obtain ⟨⟨κ, hκ⟩, hpull⟩ := coef_twistPull hL R _ hB D A G hG U F E hinj (k * n ^ 2) k hk hpos
    (by rw [eG]; exact exists_gen_mulPull_pow_unif R _ D A G U.toUnifPre n k _ rfl)
  have hAct : E.Act h p.g := (eAct F _ _).2 hh
  obtain ⟨α₀, hα₀⟩ := hL.1.mulPull _ A n
  have e₁ : (snd (TFK (R := R) F) A.A).left ≫ (mulA A.A n).left = (snd (TFK (R := R) F) A.A ^ n).left := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  obtain ⟨α₁, hα₁, -⟩ := exists_gen A.isLB
    (φ' := ![(snd (TFK (R := R) F) A.A).left, (snd (TFK (R := R) F) A.A ^ n).left])
    (ε' := ![((k * n ^ 2 : ℕ) : ℤ), -(k : ℤ)])
    (fun U _ f => by
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Category.comp_id, e₁]
      congr 2 <;> push_cast <;> ring)
    (GeneratorPullback.powGen A.L _ _ (LB.pullGen A.L _ _ α₀ (snd (TFK (R := R) F) A.A).left) k)
    (powGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ hα₀ _) k)
  obtain ⟨α, hα, hαn⟩ := GlobalTheory.NormTheta.exists_normalised A.isLB hN.2.1 n _ _ _ rfl α₁ hα₁
  obtain ⟨t', ht'⟩ := GlobalTheory.VVRank.exists_isTwistPull A.A (ψ := mulT A.A _ n) (hm := lift_snd _ _) A.isLB hα t
  obtain ⟨s', hs', -⟩ := ((GlobalTheory.TorsionAnyChar.expBijF_any hL R _ hB D A G hG U).1 F _ hpos w₀ hN.1).1 t'
  obtain ⟨W', hW'⟩ := (coef_basic R D.toPre F (k * n ^ 2) h).1
  obtain ⟨w, hw, hwv⟩ := TorsionValue.exists_frm_kap hAct.1 W' hW' κ hκ.1
  obtain ⟨h₁, h₂⟩ := hpull w₀ ρ hN (mulT A.A _ n) (snd _ A.A ^ n) (lift_snd _ _) (lift_fst _ _)
    (by rw [eA, MonObj.comp_pow, Category.comp_id]) α hα hαn t t' s s' hs hs' ht' κ hκ h p.g hAct W' w hW' hw hwv
  obtain ⟨z₀⟩ := exists_pt (R := R) (F := F)
  obtain ⟨e, he⟩ : ∃ e : FrAt x, e.IsGen := exists_gen_pt A.isLB z₀ (fun y => pt_eq y z₀) _ _
  obtain ⟨c, hc⟩ := GlobalTheory.OneBasis.exists_valAt A F hL.1 t' x he
  obtain ⟨l, -, H⟩ := value_at_level hB hG U hN hpos q x hx' e he W' hW'
  have S := ((sumF_calculus R I hB F _ _ (fun _ => 0) _ 0).2.2 _ E.h hinj h₂).2 (H t' s' c hs' hc)
  obtain ⟨d, -, -, hdc⟩ := ((coef_basic R D.toPre F k p.g).2.2 w hw).2.2.1 W hW
  have S' := sumF_smul hB d S
  simp only [Function.comp_apply, h₁, ← hdc] at S'
  exact ⟨_, S'⟩

omit [CharZero R] [IsAlgClosed F] in

theorem exists_coef_ratio (U : Unif I D A G) {w₀ w₁ : W0 U.toUnifPre} (h₀ : w₀.IsGen) (h₁ : w₁.IsGen) (k : ℕ) :
    ∃ d : F, d ≠ 0 ∧ ∀ (t : SecA A F k) s, U.ExpandsF F k w₀ t s → ∃ s', U.ExpandsF F k w₁ t s' ∧
      ∀ (g : GtPtF D.toPre F) (w : Frm D.toPre F k g.b), w.IsGen → coef s g w = fun χ => d * coef s' g w χ := by
  obtain ⟨d, hd, H⟩ := GlobalTheory.ExpFieldCompare.exists_expandsF_scale U.toUnifPre F k ⟨w₁, h₁⟩ ⟨w₀, h₀⟩
  refine ⟨d⁻¹, inv_ne_zero hd, fun t s hs => ⟨d • s,
    (GlobalTheory.ExpFieldCompare.expandsF_iff U.toUnifPre F ⟨w₁, h₁⟩ t _).2
      (H t s ((GlobalTheory.ExpFieldCompare.expandsF_iff U.toUnifPre F ⟨w₀, h₀⟩ t _).1 hs)), fun g w hw => funext fun χ => ?_⟩⟩
  have lin := ((coef_basic R D.toPre F k g).2.2 w hw).2.1
  have a := lin s s (d - 1) χ
  rw [show (d - 1) • s + s = d • s by rw [sub_smul, one_smul, sub_add_cancel]] at a
  rw [a]
  field_simp
  ring

end Unif

open GlobalTheory.UT.CoefBasic in
attribute [local instance] TorusExt.gtGroup in

theorem liesOver_of_qkToAkU : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif I D A G) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ (k : ℕ), 1 ≤ k → ∀ (p : QkPt D.toPre F k) (x : TFK (R := R) F ⟶ A.A), p.y = 0 → QkToAkU U.toUnifPre F k p x → ∃ (w : Frm D.toPre F 1 p.g.b) (fr : FrAt x), w.IsGen ∧ fr.IsGen ∧ GlobalTheory.Poinc.Tors.LiesOver U.toUnifPre w₀ p.g w x fr := by
  intro R _ _ _ I hB D A G _ _ hG U F _ _ _ w₀ hw₀ n hn p x hp hx
  have hL := GlobalTheory.firstFiveLaws
  have hbij := (GlobalTheory.TorsionAnyChar.expBijF_any hL R _ hB D A G hG U).1 F
  obtain ⟨⟨ρ, hρ⟩, hnorm, -⟩ := sumF_origin hL R _ hB D A G hG U F
  obtain ⟨u₀, hN⟩ := hnorm ρ hρ
  obtain ⟨z₀⟩ := exists_pt (R := R) (F := F)
  obtain ⟨e, he⟩ : ∃ e : FrAt x, e.IsGen := exists_gen_pt A.isLB z₀ (fun y => pt_eq y z₀) _ _
  obtain ⟨ω, hω⟩ := (coef_basic R D.toPre F 1 p.g).1
  choose Ω hΩ hΩv using TorsionValue.exists_frm_pow ω hω
  have pf : ∀ (k : ℤ) z J, val (powFrame A.A A.L x e k) (𝟙 _) z J = val e (𝟙 _) z J ^ k := fun k z J => map_zpow _ _ _
  obtain ⟨l, hl, H⟩ := exists_degree_constant hB (fun k a c => ∃ (t : SecA A F k) (s : Fam D.toPre F k),
      U.ExpandsF F k w₀ t s ∧ ValAt t x e c ∧ a = coef s p.g (Ω k)) n hn
    (by
      rintro k _ c hk ⟨t, s, hs, -, rfl⟩
      obtain ⟨d, -, hd⟩ := exists_coef_ratio (F := F) U hw₀ hN.1 k
      obtain ⟨s', hs', e'⟩ := hd t s hs
      obtain ⟨r, hr⟩ := exists_sumF hB hG U hN hn p hp hk (Ω k) (hΩ k) t s' hs'
      rw [e' _ _ (hΩ k)]
      exact ⟨_, sumF_smul hB d hr⟩)
    (by
      rintro k k' _ _ c c' hk hk' ⟨t, s, hs, ht, rfl⟩ ⟨t', s', hs', ht', rfl⟩
      obtain ⟨t'', h''⟩ := TorsionValue.exists_secA_mul t t'
      obtain ⟨s'', hs'', -⟩ := (hbij (k + k') (by omega) w₀ hw₀).1 t''
      refine ⟨_, ⟨t'', s'', hs'', fun z J hJ => ?_, rfl⟩, fun α =>
        (GlobalTheory.TorsionAnyChar.prodConv_any hL R _ hB D A G hG U F w₀ hw₀ k k' _ hk hk' rfl t t' t'' s s' s'' hs hs' hs''
          (fun z J hJ => h'' _ _ z J hJ) p.g _ _ _ (hΩ k) (hΩ k') (hΩ _)
          (fun z J hJ => by rw [hΩv _ z J hJ, hΩv _ z J hJ, hΩv _ z J hJ, pow_add]) α)⟩
      have cm : @id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z (c * c')) =
          @id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z c) *
            @id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z c') :=
        (cst_eq (R := R) z _).trans ((map_mul _ _ _).trans
          (congrArg₂ (· * ·) (cst_eq (R := R) z _).symm (cst_eq (R := R) z _).symm))
      rw [h'' _ _ z J hJ, ht z J hJ, ht' z J hJ, pf, pf, pf, cm, Nat.cast_add, zpow_add, Units.val_mul]
      ring)
    (fun k hk => by
      obtain ⟨t, c, hc, ht⟩ := NonVan.exists_sec_ne_zero hL R A F k hk x e he
      obtain ⟨s, hs, -⟩ := (hbij k (by omega) w₀ hw₀).1 t
      exact ⟨_, c, ⟨t, s, hs, ht, rfl⟩, hc⟩)
    (fun m hm => by
      let q : QkPt D.toPre F (n * m) := TorusExt.qkMk D.tau_bimult (m • p.y) p.g (by
        rw [mul_nsmul, TorusExt.qk_nsmul D.tau_bimult p, map_nsmul])
      have hq : QkToAkU U.toUnifPre F (n * m) q x :=
        ((GlobalTheory.LevelCompat.qkToAkU_level hL R _ hB D A G hG U F n m _ hn hm rfl p q x).1 rfl rfl).1 hx
      obtain ⟨κ, hκ, Hκ⟩ := value_at_level hB hG U hN (Nat.mul_pos hn hm) q x hq e he (Ω _) (hΩ _)
      obtain ⟨d, hd0, hd⟩ := exists_coef_ratio (F := F) U hw₀ hN.1 (n * m)
      refine ⟨d * κ, mul_ne_zero hd0 hκ, ?_⟩
      rintro _ c ⟨t, s, hs, ht, rfl⟩
      obtain ⟨s', hs', e'⟩ := hd t s hs
      rw [e' _ _ (hΩ _), _root_.mul_assoc]
      exact sumF_smul hB d (Hκ t s' c hs' ht))
  obtain ⟨w₁, hw₁, hv₁⟩ := TorsionValue.exists_frm_scale ω hω (inv_ne_zero hl)
  refine ⟨w₁, e, hw₁, he, fun k hk w hwv hw t s c hs ht => ?_⟩
  have S := sumF_smul hB (l⁻¹ ^ k) (H k _ c hk ⟨t, s, hs, ht, rfl⟩)
  have sc := TorsionValue.coef_scale (w' := w) (hΩ k) (c := l⁻¹ ^ k) (fun z J hJ => by
    rw [hwv z J hJ, hΩv k z J hJ, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hv₁ z J hJ, mul_pow,
      cst_eq, cst_eq, map_pow]) s
  rw [← _root_.mul_assoc, ← mul_pow, inv_mul_cancel₀ hl, one_pow, _root_.one_mul] at S
  simpa only [← sc] using S

end GlobalTheory.Poinc.Tors.ValPair
end
