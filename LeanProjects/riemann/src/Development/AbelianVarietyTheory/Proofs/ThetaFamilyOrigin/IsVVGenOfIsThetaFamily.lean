import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverOfSubsingleton

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

def labelSymp {g M : ℕ} (a b : Fin (2 * g) → ZMod M) : ZMod M :=
  ∑ i, ∑ j, a i * b j * (stdSymp g i j : ℤ)

def thetaCoordIdx {g M : ℕ} (m r : ℕ) (a c : Fin (2 * g) → ZMod M) : Fin (2 * g) → ZMod M := r • a + m • c

def thetaCoordExp {g M : ℕ} (m r : ℕ) (a c : Fin (2 * g) → ZMod M) : ℕ :=
  ((((M + 1) / 2 : ℕ) : ZMod M) * labelSymp (m • c) (r • a)).val

def thetaRelExp {g M : ℕ} (m r : ℕ) (a b : Fin (2 * g) → ZMod M) : ℕ :=
  ((((m ^ 2 + 1) / 2 : ℕ) : ZMod M) * labelSymp a ((r ^ 2 * m) • b)).val

def IsThetaFamily {S : Scheme.{0}} (P : PolAV S) (N m : ℕ) {T : Over S} {I : Type} (x : I → (T ⟶ P.A))
    (th : LB.Sec (LPow P.A P.L 1 T)) (t : I → LB.Sec (LPow P.A P.L N T)) : Prop :=
  ∃ (s₁ : LB.Sec (LPow P.A P.L N T))
    (α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd T P.A).left, (snd T P.A ^ m).left] ![(N : ℤ), -1]))
    (U : I → ThetaGrp P.A P.L N T),
    α.IsGen ∧ IsTwistPull P.A P.L (mulT P.A T m) (snd T P.A ^ m) (lift_snd _ _) N 1 α th s₁ ∧
    (∀ i, SymLift P.A P.L N N (x i) (U i)) ∧ ∀ i, IsActOf P.A P.L N (U i) s₁ (t i)

namespace ThetaCoord

open CommPairing GlobalLift VVRank

variable {S : Scheme.{0}} {T T' : Over S}

theorem isThetaFamily_pull {P : PolAV S} {N m : ℕ} {I : Type} {x : I → (T ⟶ P.A)} {th t}
    (H : IsThetaFamily P N m x th t) (h : T' ⟶ T) :
    IsThetaFamily P N m (fun i => h ≫ x i) (pullS P.A 1 h th) (fun i => pullS P.A N h (t i)) := by
  obtain ⟨s₁, α, U, hα, hs, hU, ht⟩ := H
  obtain ⟨α', hα', k₁⟩ := exists_twist_pull P.A (ψ := mulT P.A T m) (hm := lift_snd _ _) (b := 1)
    P.isLB hα h (ψ' := mulT P.A T' m) (lift_snd _ _) (mulT_comm P.A h m)
  choose U' hU' k₃ using fun a => exists_symLift_act_pull P.isLB h (hU a)
  exact ⟨_, α', U', hα', k₁ _ _ hs, hU', fun i => k₃ i _ _ (ht i)⟩

section Labels

variable {A : Over S} [GrpObj A] [IsCommMonObj A] {n M : ℕ} [NeZero M] {pt : Fin n → (T ⟶ A)}

abbrev lab (pt : Fin n → (T ⟶ A)) (a : Fin n → ZMod M) : T ⟶ A := linComb pt fun i => (a i).val

theorem lab_add (h : ∀ i, pt i ^ M = 1) (a b : Fin n → ZMod M) : lab pt (a + b) = lab pt a * lab pt b := by
  simp only [lab, linComb, List.prod_ofFn, ← Finset.prod_mul_distrib, ← pow_add, Pi.add_apply, ZMod.val_add]
  exact Finset.prod_congr rfl fun i _ => (pow_eq_pow_mod _ (h i)).symm

omit [NeZero M] in
theorem lab_zero : lab pt (0 : Fin n → ZMod M) = 1 := by
  simp [lab, linComb]

theorem lab_nsmul (h : ∀ i, pt i ^ M = 1) (k : ℕ) (a : Fin n → ZMod M) : lab pt (k • a) = lab pt a ^ k := by
  induction k with
  | zero => rw [zero_smul, lab_zero, pow_zero]
  | succ k ih => rw [succ_nsmul, lab_add h, ih, pow_succ]

omit [NeZero M] in
theorem lab_pow (h : ∀ i, pt i ^ M = 1) (a : Fin n → ZMod M) : lab pt a ^ M = 1 := linComb_pow _ _ _ h

omit [NeZero M] in
theorem lab_single (h : ∀ i, pt i ^ M = 1) (i : Fin n) : lab pt (Pi.single i (1 : ZMod M)) = pt i := by
  rw [lab, linComb, List.prod_ofFn, Finset.prod_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne hj])
    (by simp), Pi.single_eq_same, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod _ (h i), pow_one]

end Labels

theorem char_ext {n M : ℕ} [NeZero M] {U : Type} [CommGroup U] (f f' : (Fin n → ZMod M) → U)
    (hf : ∀ a b, f (a + b) = f a * f b) (hf' : ∀ a b, f' (a + b) = f' a * f' b)
    (h : ∀ i, f (Pi.single i 1) = f' (Pi.single i 1)) (a : Fin n → ZMod M) : f a = f' a := by
  let F : (Fin n → ZMod M) →+ Additive U := AddMonoidHom.mk' (fun a => Additive.ofMul (f a)) hf
  let F' : (Fin n → ZMod M) →+ Additive U := AddMonoidHom.mk' (fun a => Additive.ofMul (f' a)) hf'
  have e : a = ∑ i, (a i).val • Pi.single i (1 : ZMod M) := by
    refine (Finset.univ_sum_single a).symm.trans (Finset.sum_congr rfl fun i _ => ?_)
    rw [← Pi.single_smul, nsmul_one, ZMod.natCast_zmod_val]
  have : F a = F' a := by
    rw [e, map_sum, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_nsmul, map_nsmul]; exact congrArg _ (h i)
  exact this

theorem pow_val_add {M : ℕ} [NeZero M] {U : Type} [Monoid U] {ζ : U} (h : ζ ^ M = 1) (a b : ZMod M) :
    ζ ^ (a + b).val = ζ ^ a.val * ζ ^ b.val := by
  rw [ZMod.val_add, ← pow_eq_pow_mod _ h, pow_add]

theorem pow_val_mul {M : ℕ} [NeZero M] {U : Type} [Monoid U] {ζ : U} (h : ζ ^ M = 1) (k : ℕ) (a : ZMod M) :
    ζ ^ ((k : ZMod M) * a).val = (ζ ^ a.val) ^ k := by
  rw [ZMod.val_mul, ← pow_eq_pow_mod _ h, ZMod.val_natCast, Nat.mul_comm, pow_mul, ← pow_eq_pow_mod]
  rw [← pow_mul, Nat.mul_comm, pow_mul, h, one_pow]

theorem weilIs_lab (hG : GlobalFnsSt) (P : PolAV S) {g M : ℕ} [NeZero M] {pt : Fin (2 * g) → (T ⟶ P.A)}
    (h : ∀ i, pt i ^ M = 1) {ze : Γ(T.left, ⊤)ˣ} (hze : ze ^ M = 1)
    (hp : ∀ i j, WeilIs P.A P.L M (pt i) (pt j) (ze ^ stdSymp g i j))
    (hex : ∀ a b : Fin (2 * g) → ZMod M, ∃ c, WeilIs P.A P.L M (lab pt a) (lab pt b) c)
    (a b : Fin (2 * g) → ZMod M) : WeilIs P.A P.L M (lab pt a) (lab pt b) (ze ^ (labelSymp a b).val) := by
  have := P.isAb.comm
  choose c hc using hex
  have un : ∀ {x y : T ⟶ P.A} {c c'}, WeilIs P.A P.L M x y c → WeilIs P.A P.L M x y c' → c = c' := fun H H' =>
    CommutatorPairing.weilIs_unique hG P.isAb P.isLB H H'
  have h₁ : ∀ a a' b, c (a + a') b = c a b * c a' b := fun a a' b =>
    un (hc _ _) (by rw [lab_add h]; exact weilIs_mul_left hG S P M T _ _ _ _ _ (hc a b) (hc a' b))
  have h₂ : ∀ a b, c a b = (c b a)⁻¹ := fun a b => un (hc _ _) (weilIs_symm P.isLB (hc b a))
  rw [← char_ext (fun a => c a b) (fun a => ze ^ (labelSymp a b).val) (fun _ _ => h₁ _ _ _)
    (fun a a' => by
      rw [← pow_val_add hze]; simp only [labelSymp, Pi.add_apply, add_mul, Finset.sum_add_distrib])
    (fun i => char_ext (fun b => c (Pi.single i 1) b) (fun b => ze ^ (labelSymp (Pi.single i 1) b).val)
      (fun b b' => by rw [h₂, h₁, mul_inv, ← h₂, ← h₂])
      (fun a a' => by
        rw [← pow_val_add hze]; simp only [labelSymp, Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib])
      (fun j => ?_) b) a]
  · exact hc a b
  have e : labelSymp (Pi.single i (1 : ZMod M)) (Pi.single j 1) = (stdSymp g i j : ℤ) := by
    simp [labelSymp, Pi.single_apply]
  have := hc (Pi.single i 1) (Pi.single j 1)
  rw [lab_single h, lab_single h] at this
  rw [un this (hp i j), e, ← zpow_natCast, ZMod.val_intCast]
  exact zpow_eq_zpow_emod _ (by rw [zpow_natCast, hze])

theorem coord_over (hG : GlobalFnsSt) (P : PolAV S) {g m r N N' : ℕ} (hN : N = m ^ 2) (hN' : N' = r * m) (ho : Odd N')
    {pt : Fin (2 * g) → (T ⟶ P.A)} (h : ∀ i, pt i ^ (N' ^ 2) = 1) {ze : Γ(T.left, ⊤)ˣ} (hze : ze ^ (N' ^ 2) = 1)
    (hp : ∀ i j, WeilIs P.A P.L (N' ^ 2 : ℕ) (pt i) (pt j) (ze ^ stdSymp g i j))
    {v : (Fin (2 * g) → ZMod (N' ^ 2)) → Γ(T.left, ⊤)} (hv : IsThetaPtOver P N' (lab pt) v) :
    ∃ th', IsGenSec P.A P.L 1 th' ∧ ∀ th t (ρ : Γ(T.left, ⊤)), SecM.ofSec P.A th = ρ • SecM.ofSec P.A th' →
      IsThetaFamily P N m (fun a : Fin (2 * g) → ZMod (N' ^ 2) => lab pt a ^ r ^ 2) th t →
      ∀ (c : Fin (2 * g) → ZMod (N' ^ 2))
        (τ : LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => (lab pt c ^ N').left) (fun _ => (N : ℤ)))),
        τ.IsGen → ∃ u : Γ(T.left, ⊤)ˣ, ∀ a, IsValueAt P.A P.L N (t a) (lab pt c ^ N') τ
          (ρ * u * (ze ^ thetaCoordExp m r a c : Γ(T.left, ⊤)ˣ) * v (thetaCoordIdx m r a c)) := by
  have := P.isAb.comm
  have : NeZero (N' ^ 2) := ⟨ho.pow.pos.ne'⟩
  obtain ⟨th', s', α', τ₀, W, t', w, u₀, hth, hα', hτ₀, hs', hW, ht', hw, hvw⟩ := hv
  refine ⟨th', hth, fun th t ρ hρ ⟨s, α, U, hα, hs, hU, ht⟩ c τ hτ => ?_⟩
  have hc := weilIs_lab hG P h hze hp fun a b => by
    obtain ⟨c, hc⟩ := CommutatorPairing.exists_commIsOf hG P.isAb P.isLB (W a) (W b)
    have := weilIs_of_commIsOf hG P.isAb P.isLB hc
    rw [(hW a).pt_eq, (hW b).pt_eq, ← Nat.cast_pow] at this
    exact ⟨c, this⟩
  rw [Nat.cast_pow] at hc
  obtain ⟨u, hu⟩ := exists_unit_isValueAt hG P.isAb P.isLB hN' (q := N) (q' := N' ^ 2)
    ⟨r ^ 2, by rw [hN, hN']; ring⟩ ho.pow hρ hα hα' hs hs' hτ₀ (Z := lab pt (m • c)) (h := lab pt c ^ N')
    (by rw [lab_nsmul h, ← pow_mul, Nat.mul_comm m r, ← hN']) (hW _) hτ
  refine ⟨u * u₀⁻¹, fun a => ?_⟩
  have := hu (lab pt (r • a)) (U a) (t a) (W (r • a + m • c)) (t' _) (w _) _ (lab_pow h _)
    (by rw [lab_nsmul h, ← pow_mul, ← sq]; exact hU a) (ht a) (by rw [← lab_add h]; exact hW _) (ht' _) (hw _)
    (hc _ _)
  convert this using 1
  rw [thetaCoordExp, pow_val_mul hze, thetaCoordIdx, hvw, Units.val_mul]
  linear_combination (ρ * u * (((ze ^ (labelSymp (m • c) (r • a)).val) ^ ((N' ^ 2 + 1) / 2) : Γ(T.left, ⊤)ˣ) :
    Γ(T.left, ⊤)) * w (r • a + m • c)) * u₀.inv_mul

theorem relation [IsLocallyNoetherian S] (hG : GlobalFnsSt) (hWe : WeilSt) (P : PolAV S) {g m r N N' : ℕ}
    (hN : N = m ^ 2) (hN' : N' = r * m) (ho : Odd N') (hu : IsUnit (N' : Γ(T.left, ⊤)))
    {pt : Fin (2 * g) → (T ⟶ P.A)} (h : ∀ i, pt i ^ (N' ^ 2) = 1) {ze : Γ(T.left, ⊤)ˣ} (hze : ze ^ (N' ^ 2) = 1)
    (hp : ∀ i j, WeilIs P.A P.L (N' ^ 2 : ℕ) (pt i) (pt j) (ze ^ stdSymp g i j)) {th t}
    (H : IsThetaFamily P N m (fun a : Fin (2 * g) → ZMod (N' ^ 2) => lab pt a ^ r ^ 2) th t)
    (a b : Fin (2 * g) → ZMod (N' ^ 2)) :
    SecM.ofSec P.A (t a) =
      ((ze ^ thetaRelExp m r a b : Γ(T.left, ⊤)ˣ) : Γ(T.left, ⊤)) • SecM.ofSec P.A (t (a + m • b)) := by
  have := P.isAb.comm
  have : NeZero (N' ^ 2) := ⟨ho.pow.pos.ne'⟩
  obtain ⟨s, α, U, hα, hs, hU, ht⟩ := H
  have e : N * r ^ 2 = N' ^ 2 := by rw [hN, hN']; ring
  have hoN : Odd N := by rw [hN]; exact (Nat.odd_mul.1 (hN' ▸ ho)).2.pow
  have hc := weilIs_lab hG P h hze hp
    (fun a b => ((hWe S P _ T).1 _ _ (lab_pow h a) (lab_pow h b)).exists) a ((r ^ 2 * m) • b)
  have e₁ : lab pt ((r ^ 2 * m) • b) = lab pt (m • b) ^ r ^ 2 := by rw [mul_smul, lab_nsmul h]
  have hm : (lab pt (m • b) ^ r ^ 2) ^ m = 1 := by
    rw [lab_nsmul h, ← pow_mul, ← pow_mul, show m * (r ^ 2 * m) = N' ^ 2 by rw [hN']; ring, lab_pow h]
  have hy : (lab pt (m • b) ^ r ^ 2) ^ N = 1 := by rw [hN, sq m, pow_mul, hm, one_pow]
  rw [e₁] at hc
  have hc' := ((hWe S P N T).2.2.2 (r ^ 2) (lab pt a) _ _ (by rw [e, Nat.cast_pow]; exact hu.pow 2)
    (by rw [e, lab_pow h]) hy).1 (by rw [← Nat.cast_mul, e]; exact hc)
  obtain ⟨ν, hν⟩ := exists_gen_negLB hG S P 1 T
  rw [thetaRelExp, pow_val_mul hze, ← hN]
  exact ofSec_act_act hG P.isAb P.isLB hoN hy (hU a) (hU (m • b))
    (by rw [← mul_pow, ← lab_add h, add_comm]; exact hU _) hc'
    (isActOf_self hG P.isAb P.isLB hoN hν hα hs hm hy (hU (m • b))) (ht a) (ht _)

section Level

variable {P : PolAV S} {M : ℕ} {ze : Γ(S, ⊤)ˣ} (lev : Level P M ze) {g : ℕ} (hg : P.g = g)

theorem levelPoint_eq_lab : levelPoint lev hg = lab (levelBasis lev hg) := by subst hg; rfl

theorem levelBasis_pow (i : Fin (2 * g)) : levelBasis lev hg i ^ M = 1 := lev.torsion _

theorem weilIs_levelBasis (i j : Fin (2 * g)) :
    WeilIs P.A P.L M (levelBasis lev hg i) (levelBasis lev hg j) (ze ^ stdSymp g i j) := by
  subst hg; exact lev.pairing i j

end Level

theorem pow_eq_one_iff {K : Type} [Field K] [IsAlgClosed K] {P : PolAV (Spec (CommRingCat.of K))} {M d e : ℕ}
    [NeZero M] (hM : M = d * e) {ze : Γ(Spec (CommRingCat.of K), ⊤)ˣ} (lev : Level P M ze) {g : ℕ} (hg : P.g = g)
    (x : baseOver _ ⟶ P.A) : x ^ d = 1 ↔ ∃ a, levelPoint lev hg a ^ e = x := by
  subst hg
  have := P.isAb.comm
  have h := lev.torsion
  have E : ∀ c : Fin (2 * P.g) → ℕ, linComb (fun i => (Over.homMk (𝟙 _) (by simp) : Over.mk (𝟙 _) ⟶ baseOver _) ≫ lev.pt i) c =
      linComb lev.pt c := fun c => congrArg (linComb · _) (funext fun i => Category.id_comp (lev.pt i))
  refine ⟨fun hx => ?_, ?_⟩
  · obtain ⟨c, hc⟩ := lev.span K (𝟙 _) x (by rw [hM, pow_mul, hx, one_pow])
    replace hc := (E _).symm.trans hc
    let a : Fin (2 * P.g) → ZMod M := fun i => (c i : ℕ)
    have ha : lab lev.pt a = x :=
      (congrArg (linComb _) (funext fun i => ZMod.val_cast_of_lt (c i).2)).trans hc
    have h₀ := lev.indep K (𝟙 _) (fun i => ⟨((d • a) i).val, ZMod.val_lt _⟩)
      (fun i => ⟨(0 : ZMod M).val, ZMod.val_lt _⟩) ((E _).trans
        ((((lab_nsmul h d a).trans (ha ▸ hx)).trans (lab_zero (M := M)).symm).trans (E _).symm))
    have hd : 0 < d := Nat.pos_of_ne_zero fun h => NeZero.ne M (by rw [hM, h, zero_mul])
    have h₁ : ∀ i, e ∣ (c i : ℕ) := fun i => by
      have q : (d • a) i = 0 := ZMod.val_injective M (congrArg Fin.val (congrFun h₀ i))
      rw [Pi.smul_apply, nsmul_eq_mul, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff] at q
      exact Nat.dvd_of_mul_dvd_mul_left hd (hM ▸ q)
    refine ⟨fun i => ((c i : ℕ) / e : ℕ), ((lab_nsmul h e _).symm.trans (congrArg _ (funext fun i => ?_))).trans ha⟩
    rw [Pi.smul_apply, nsmul_eq_mul, ← Nat.cast_mul, Nat.mul_div_cancel' (h₁ _)]
    rfl
  · rintro ⟨a, rfl⟩
    rw [← pow_mul, Nat.mul_comm, ← hM]
    exact lab_pow h a

theorem exists_isThetaFamily (hLaw : Laws) [IsLocallyNoetherian S] [Subsingleton T.left] [Nonempty T.left]
    (P : PolAV S) {m N : ℕ} (hN : N = m ^ 2) (ho : Odd N) (hu : IsUnit (N : Γ(S, ⊤))) {I : Type}
    (x : I → (T ⟶ P.A)) (hx : ∀ i, x i ^ N = 1) (th : LB.Sec (LPow P.A P.L 1 T)) :
    ∃ t, IsThetaFamily P N m x th t := by
  obtain ⟨p⟩ := ‹Nonempty T.left›
  have H := hLaw.mulPull S P m
  rw [← Nat.cast_pow, ← hN] at H
  obtain ⟨α₀, hα₀⟩ := H
  obtain ⟨α, hα, -⟩ := exists_gen_pullTo (φ' := ![(snd T P.A).left, (snd T P.A ^ m).left]) α₀ hα₀
    (snd T P.A).left (fun k => by
      fin_cases k
      · exact Category.comp_id _
      · change (snd T P.A).left ≫ (mulA P.A m).left = (snd T P.A ^ m).left
        rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id])
  obtain ⟨s₁, hs₁⟩ := exists_isTwistPull P.A (ψ := mulT P.A T m) (hm := lift_snd _ _) (b := 1) P.isLB hα th
  have hU : ∀ i, ∃ θ : ThetaGrp P.A P.L N T, SymLift P.A P.L N N (x i) θ := fun i => by
    obtain ⟨V, hV, θ, hθ⟩ := (hLaw.symLift S P N ho hu T (x i) (hx i)).1 p
    obtain ⟨h, e⟩ := exists_section hV
    obtain ⟨θ', H'⟩ := exists_symLift_pull P.isLB h hθ
    rw [← Category.assoc, e, Category.id_comp] at H'
    exact ⟨θ', H'⟩
  choose U hU using hU
  choose t ht using fun i => (exists_isTwistPull P.A P.isLB (U i).isGen s₁ : ∃ y, IsActOf P.A P.L (N : ℤ) (U i) s₁ y)
  exact ⟨t, s₁, α, U, hα, hs₁, hU, ht⟩

theorem span_eq_top (hLaw : Laws) {K : Type} [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) {m N : ℕ}
    (hN : N = m ^ 2) (hK : (N : K) ≠ 0) {I : Type} {x : I → (baseOver _ ⟶ P.A)}
    (hx : ∀ y : baseOver _ ⟶ P.A, y ^ N = 1 → ∃ i, x i = y) {th t} (hth : IsGenSec P.A P.L 1 th)
    (H : IsThetaFamily P N m x th t) :
    Submodule.span Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤) (Set.range fun i => SecM.ofSec P.A (t i)) = ⊤ := by
  obtain ⟨s, α, U, hα, hs, hU, ht⟩ := H
  have hN0 : N ≠ 0 := fun h => hK (by rw [h, Nat.cast_zero])
  have hm0 : m ≠ 0 := fun h => hN0 (by rw [hN, h]; rfl)
  have hk : N = 1 ∨ 4 ≤ N := by
    rcases Nat.lt_or_ge m 2 with h | h
    · left; rw [hN, show m = 1 by omega]; rfl
    · right; nlinarith
  have : Nonempty I := ⟨(hx 1 (one_pow _)).choose⟩
  obtain ⟨ρ, k₁, -, k₃, k₄⟩ := thetaGrp_acts_linearly hLaw.globalFns _ P N (baseOver _)
  simp only [← fun i => (k₁ _ _ _).1 (ht i)]
  refine span_translates_eq_top P.A (hLaw.irred K P N hk hK) ρ k₁ k₃ k₄ U (fun θ => ?_) _ fun h0 => ?_
  · obtain ⟨i, hi⟩ := hx θ.pt ((hLaw.kerPow _ P N (by omega) _ θ.pt).1 fun _ =>
      ⟨⊤, trivial, _, LB.isGen_genPull _ θ.φ θ.isGen _⟩)
    exact ⟨i, (hU i).pt_eq.trans hi⟩
  · have hint : IsIntegral (baseOver _ ⊗ P.A).left :=
      (forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ P.A.hom P.isAb.smooth
        P.isAb.geomConnected).geometrically_isIntegral (𝟙 _) _ _ (IsPullback.of_hasPullback (𝟙 _) P.A.hom).flip
    have hz := ofSec_eq_zero_of_twist P.A P.isLB
      (surjective_mulT P.A m (hLaw.mulN _ P m (by omega)).2.2.1 _) hs h0
    have : Subsingleton (SecM P.A P.L (1 : ℕ) (baseOver (Spec (CommRingCat.of K)))) :=
      subsingleton_of_forall_eq 0 fun y => by
        obtain ⟨r, hr⟩ := hth (SecM.toSec P.A y)
        have e : y = r • SecM.ofSec P.A th := Subtype.ext (funext hr)
        exact e.trans ((congrArg (r • ·) hz).trans (smul_zero r))
    have hnt : Nontrivial Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom.domain_nontrivial
    have := hLaw.globalSectionsRank K P 1 le_rfl
    rw [Module.finrank_zero_of_subsingleton, one_pow] at this
    exact zero_ne_one this

theorem exists_basis_of_relation {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] {n M m : ℕ} [NeZero M]
    (hm : 0 < m) (u : (Fin n → ZMod M) → (Fin n → ZMod M) → Rˣ) (t : (Fin n → ZMod M) → V)
    (hr : ∀ a b, t a = (u a b : R) • t (a + m • b)) (hs : Submodule.span R (Set.range t) = ⊤)
    (hd : Module.finrank R V = m ^ n) :
    ∃ B : Module.Basis (Fin n → Fin m) R V, (∀ e, B e = t fun i => (e i : ℕ)) ∧
      ∀ a, t a = ((u (fun i => ((a i).val % m : ℕ)) (fun i => ((a i).val / m : ℕ)))⁻¹ : Rˣ) •
        B fun i => ⟨(a i).val % m, Nat.mod_lt _ hm⟩ := by
  have key : ∀ a : Fin n → ZMod M, t a = ((u (fun i => ((a i).val % m : ℕ)) (fun i => ((a i).val / m : ℕ)))⁻¹ : Rˣ) •
      t fun i => ((a i).val % m : ℕ) := fun a => by
    rw [hr (fun i => ((a i).val % m : ℕ)) (fun i => ((a i).val / m : ℕ)), ← Units.smul_def, inv_smul_smul]
    refine congrArg t (funext fun i => ?_)
    rw [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, ← Nat.cast_mul, ← Nat.cast_add, Nat.mod_add_div,
      ZMod.natCast_zmod_val]
  have hs' : ⊤ ≤ Submodule.span R (Set.range fun e : Fin n → Fin m => t fun i => (e i : ℕ)) := by
    rw [← hs, Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    rw [key]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨fun i => ⟨(a i).val % m, Nat.mod_lt _ hm⟩, rfl⟩)
  exact ⟨Module.Basis.mk (linearIndependent_of_top_le_span_of_card_eq_finrank hs' (by simp [hd])) hs',
    fun e => Module.Basis.mk_apply _ _ _, fun a => by rw [Module.Basis.mk_apply]; exact key a⟩

theorem relation_iff {R V V' I κ : Type} [CommRing R] [AddCommGroup V] [Module R V] [AddCommGroup V'] [Module R V']
    (B : Module.Basis κ R V) (B' : Module.Basis κ R V') {t : I → V} {t' : I → V'} {u : I → Rˣ} {σ : I → κ}
    (h : ∀ a, t a = u a • B (σ a)) (h' : ∀ a, t' a = u a • B' (σ a)) (F : Finset I) (l : I → R) :
    ∑ a ∈ F, l a • t a = 0 ↔ ∑ a ∈ F, l a • t' a = 0 := by
  have q : ∀ a, B.equiv B' (Equiv.refl _) (t a) = t' a := fun a => by
    rw [h, h', Units.smul_def, Units.smul_def, map_smul, Module.Basis.equiv_apply, Equiv.refl_apply]
  rw [← (B.equiv B' (Equiv.refl _)).map_eq_zero_iff, map_sum]
  simp only [map_smul, q]

theorem exists_basis_field (hLaw : Laws) {g m r N N' : ℕ} (hN : N = m ^ 2) (hN' : N' = r * m) {K : Type} [Field K]
    [IsAlgClosed K] (ho : Odd N') (hK : (N' : K) ≠ 0) (hm : 0 < m) {P : PolAV (Spec (CommRingCat.of K))} (hg : P.g = g)
    {ze : Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤)ˣ} (lev : Level P (N' ^ 2) ze) {th t}
    (hth : IsGenSec P.A P.L 1 th) (ht : IsThetaFamily P N m (fun a => levelPoint lev hg a ^ r ^ 2) th t) :
    Submodule.span Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤) (Set.range fun a => SecM.ofSec P.A (t a)) = ⊤ ∧
    ∃ B : Module.Basis (Fin (2 * g) → Fin m) Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤)
        (SecM P.A P.L N (baseOver (Spec (CommRingCat.of K)))),
      (∀ e, B e = SecM.ofSec P.A (t fun i => (e i : ℕ))) ∧
      ∀ a, SecM.ofSec P.A (t a) =
        (ze ^ thetaRelExp (M := N' ^ 2) m r (fun i => ((a i).val % m : ℕ)) (fun i => ((a i).val / m : ℕ)))⁻¹ •
          B fun i => ⟨(a i).val % m, Nat.mod_lt _ hm⟩ := by
  have e : N' ^ 2 = N * r ^ 2 := by rw [hN, hN']; ring
  have : NeZero (N' ^ 2) := ⟨ho.pow.pos.ne'⟩
  have hmK : (m : K) ≠ 0 := fun h => hK (by rw [hN', Nat.cast_mul, h, mul_zero])
  have hNK : (N : K) ≠ 0 := by rw [hN, Nat.cast_pow]; exact pow_ne_zero _ hmK
  have hu : IsUnit (N' : Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤)) := by
    have := (IsUnit.mk0 _ hK).map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
    rwa [map_natCast] at this
  have sp := span_eq_top hLaw P hN hNK (fun y hy => (pow_eq_one_iff e lev hg y).1 hy) hth ht
  rw [levelPoint_eq_lab] at ht
  have rl := relation hLaw.globalFns hLaw.weil P hN hN' ho hu (levelBasis_pow lev hg) (ze := ze) lev.prim.pow_eq_one
    (weilIs_levelBasis lev hg) ht
  have rk : Module.finrank Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤)
      (SecM P.A P.L N (baseOver (Spec (CommRingCat.of K)))) = m ^ (2 * g) :=
    (hLaw.globalSectionsRank K P N (by rw [hN]; exact pow_pos hm 2)).trans (by rw [hN, hg, ← pow_mul])
  exact ⟨sp, exists_basis_of_relation hm (fun a b => ze ^ thetaRelExp m r a b) (fun a => SecM.ofSec P.A (t a)) rl sp rk⟩

end ThetaCoord

open ThetaCoord in

theorem theta_coordinates : Laws → ∀ (g m r N N' : ℕ), N = m ^ 2 → N' = r * m →
    (∀ (S : Scheme.{0}) [IsLocallyNoetherian S] [Subsingleton S] [Nonempty S] (P : PolAV S) (hg : P.g = g)
      (ze : Γ((baseOver S).left, ⊤)ˣ) (lev : Level P (N' ^ 2) ze)
      (v : (Fin (2 * g) → ZMod (N' ^ 2)) → Γ((baseOver S).left, ⊤)),
      IsThetaPt P N' (levelPoint lev hg) v →
      (∃ th t, IsGenSec P.A P.L 1 th ∧ IsThetaFamily P N m (fun a => levelPoint lev hg a ^ r ^ 2) th t) ∧
      ∀ th t, IsGenSec P.A P.L 1 th → IsThetaFamily P N m (fun a => levelPoint lev hg a ^ r ^ 2) th t →
        (∀ (c : Fin (2 * g) → ZMod (N' ^ 2))
          (τ : LB.Gen (LB.LinComb P.L (Y := (baseOver S).left) (K := Fin 1)
            (fun _ => (levelPoint lev hg c ^ N').left) (fun _ => (N : ℤ)))), τ.IsGen →
          ∃ u : Γ((baseOver S).left, ⊤)ˣ, ∀ a, IsValueAt P.A P.L N (t a) (levelPoint lev hg c ^ N') τ
            ((u * ze ^ thetaCoordExp m r a c : Γ((baseOver S).left, ⊤)ˣ) * v (thetaCoordIdx m r a c))) ∧
        ∀ a b, SecM.ofSec P.A (t a) =
          ((ze ^ thetaRelExp m r a b : Γ((baseOver S).left, ⊤)ˣ) : Γ((baseOver S).left, ⊤)) •
            SecM.ofSec P.A (t (a + m • b))) ∧
    ∀ (K : Type) [Field K] [IsAlgClosed K], Odd N' → (N' : K) ≠ 0 →
      ∀ (P : PolAV (Spec (CommRingCat.of K))) (hg : P.g = g)
        (ze : Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤)ˣ) (lev : Level P (N' ^ 2) ze),
        (∀ x : baseOver _ ⟶ P.A, x ^ N = 1 ↔ ∃ a, levelPoint lev hg a ^ r ^ 2 = x) ∧
        (∀ h : baseOver _ ⟶ P.A, h ^ N' = 1 ↔ ∃ c, levelPoint lev hg c ^ N' = h) ∧
        ∀ th t, IsGenSec P.A P.L 1 th → IsThetaFamily P N m (fun a => levelPoint lev hg a ^ r ^ 2) th t →
          Submodule.span Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤)
            (Set.range fun a => SecM.ofSec P.A (t a)) = ⊤ ∧
          LinearIndependent Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤)
            (fun e : Fin (2 * g) → Fin m => SecM.ofSec P.A (t fun i => (e i : ℕ))) ∧
          ∀ (P' : PolAV (Spec (CommRingCat.of K))) (hg' : P'.g = g) (lev' : Level P' (N' ^ 2) ze) th' t',
            IsGenSec P'.A P'.L 1 th' → IsThetaFamily P' N m (fun a => levelPoint lev' hg' a ^ r ^ 2) th' t' →
            ∀ (F : Finset (Fin (2 * g) → ZMod (N' ^ 2)))
              (l : (Fin (2 * g) → ZMod (N' ^ 2)) → Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤)),
              ∑ a ∈ F, l a • SecM.ofSec P.A (t a) = 0 ↔ ∑ a ∈ F, l a • SecM.ofSec P'.A (t' a) = 0 := by
  intro hLaw g m r N N' hN hN'
  have hG := hLaw.globalFns
  have e : N' ^ 2 = N * r ^ 2 := by rw [hN, hN']; ring
  refine ⟨fun S _ _ _ P hg ze lev v hv => ?_, fun K _ _ ho hK => ?_⟩
  · have := P.isAb.comm
    have : Subsingleton (baseOver S).left := ‹Subsingleton S›
    have : Nonempty (baseOver S).left := ‹Nonempty S›
    have ho := hv.1
    have hu := hv.2.1
    have : NeZero (N' ^ 2) := ⟨ho.pow.pos.ne'⟩
    replace hv := isThetaPtOver_of_subsingleton P hv
    rw [levelPoint_eq_lab] at hv ⊢
    obtain ⟨th', hth', H⟩ := coord_over hG P hN hN' ho (levelBasis_pow lev hg) (ze := ze) lev.prim.pow_eq_one
      (weilIs_levelBasis lev hg) hv
    refine ⟨?_, fun th t hth ht => ⟨fun c τ hτ => ?_, relation hG hLaw.weil P hN hN' ho hu (levelBasis_pow lev hg)
      (ze := ze) lev.prim.pow_eq_one (weilIs_levelBasis lev hg) ht⟩⟩
    · have hm : IsUnit (m : Γ(S, ⊤)) :=
        isUnit_of_mul_isUnit_right (x := (r : Γ(S, ⊤))) (by rw [← Nat.cast_mul, ← hN']; exact hu)
      obtain ⟨t, ht⟩ := exists_isThetaFamily hLaw P hN (by rw [hN]; exact (Nat.odd_mul.1 (hN' ▸ ho)).2.pow)
        (by rw [hN, Nat.cast_pow]; exact hm.pow 2)
        (fun a : Fin (2 * g) → ZMod (N' ^ 2) => lab (levelBasis lev hg) a ^ r ^ 2)
        (fun a => by rw [← pow_mul, Nat.mul_comm (r ^ 2), ← e, lab_pow (levelBasis_pow lev hg)]) th'
      exact ⟨th', t, hth', ht⟩
    · obtain ⟨ρ, hρ⟩ := exists_unit_of_isGenSec hth hth'
      obtain ⟨u, hu⟩ := H th t ρ hρ ht c τ hτ
      exact ⟨ρ * u, hu⟩
  have : NeZero (N' ^ 2) := ⟨ho.pow.pos.ne'⟩
  have hm : 0 < m := (Nat.odd_mul.1 (hN' ▸ ho)).2.pos
  refine fun P hg ze lev => ⟨pow_eq_one_iff e lev hg, pow_eq_one_iff (sq N') lev hg, fun th t hth ht => ?_⟩
  obtain ⟨sp, B, hB₀, hB⟩ := exists_basis_field hLaw hN hN' ho hK hm hg lev hth ht
  refine ⟨sp, funext hB₀ ▸ B.linearIndependent, fun P' hg' lev' th' t' hth' ht' F l => ?_⟩
  obtain ⟨-, B', -, hB'⟩ := exists_basis_field hLaw hN hN' ho hK hm hg' lev' hth' ht'
  exact relation_iff B B' hB hB' F l

end GlobalTheory
