import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

namespace UpperTheory.Gal.W2.levelStructure

section Group

variable {Γ : Type} [Group Γ]

private theorem mem_hl {K : Subgroup Γ} {h u : Γ} :
    u ∈ GlobalTheory.HeckeCorr.heckeLevel K h⁻¹ ↔ u ∈ K ∧ h * u * h⁻¹ ∈ K := by
  unfold GlobalTheory.HeckeCorr.heckeLevel
  rw [Subgroup.mem_inf, Subgroup.mem_map]
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨w, hw, rfl⟩
    convert hw using 1
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · intro hu
    refine ⟨h * u * h⁻¹, hu, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

private theorem out_rel {A B : Subgroup Γ} (x : A) :
    (x : Γ)⁻¹ * (((x : A ⧸ B.subgroupOf A).out : A) : Γ) ∈ B := by
  have h1 : ((((x : A ⧸ B.subgroupOf A).out : A) : A ⧸ B.subgroupOf A)) = (x : A ⧸ B.subgroupOf A) :=
    QuotientGroup.out_eq' _
  have h2 := QuotientGroup.eq.mp h1.symm
  rw [Subgroup.mem_subgroupOf] at h2
  simpa using h2

private theorem count_eq {K K' : Subgroup Γ} {h : Γ} (hle : K' ≤ GlobalTheory.HeckeCorr.heckeLevel K h⁻¹)
    [Fintype (K ⧸ K'.subgroupOf K)] (g : Γ) :
    (Finset.univ.filter fun u : K ⧸ K'.subgroupOf K =>
        h * (((u.out : K) : Γ)⁻¹ * g * ((u.out : K) : Γ)) ∈ K).card =
      if g ∈ DoubleCoset.doubleCoset h⁻¹ (K : Set Γ) (K : Set Γ) then
        K'.relIndex (GlobalTheory.HeckeCorr.heckeLevel K h⁻¹) else 0 := by
  classical
  have hHK : GlobalTheory.HeckeCorr.heckeLevel K h⁻¹ ≤ K := GlobalTheory.HeckeCorr.heckeLevel_le K h⁻¹
  split_ifs with hg
  · obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hg
    have key : ∀ w : K, h * ((w : Γ)⁻¹ * (a * h⁻¹ * b) * w) ∈ K ↔
        a⁻¹ * (w : Γ) ∈ GlobalTheory.HeckeCorr.heckeLevel K h⁻¹ := by
      intro w
      rw [mem_hl]
      have e1 : h * ((w : Γ)⁻¹ * (a * h⁻¹ * b) * w) = (h * (w : Γ)⁻¹ * a * h⁻¹) * (b * w) := by group
      have e2 : h * (a⁻¹ * (w : Γ)) * h⁻¹ = (h * (w : Γ)⁻¹ * a * h⁻¹)⁻¹ := by group
      rw [e1, e2, Subgroup.mul_mem_cancel_right K (K.mul_mem hb w.2), inv_mem_iff]
      exact ⟨fun hx => ⟨K.mul_mem (K.inv_mem ha) w.2, hx⟩, fun hx => hx.2⟩
    have wd : ∀ w : K, a⁻¹ * (((w : K ⧸ K'.subgroupOf K).out : K) : Γ) ∈ GlobalTheory.HeckeCorr.heckeLevel K h⁻¹ ↔
        a⁻¹ * (w : Γ) ∈ GlobalTheory.HeckeCorr.heckeLevel K h⁻¹ := by
      intro w
      obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (K'.subgroupOf K) w
      rw [hk, Subgroup.coe_mul, ← _root_.mul_assoc,
        Subgroup.mul_mem_cancel_right _ (hle (Subgroup.mem_subgroupOf.mp k.2))]
    rw [Finset.filter_congr (fun u _ => key u.out), ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    symm
    let a' : K := ⟨a, ha⟩
    let F : GlobalTheory.HeckeCorr.heckeLevel K h⁻¹ ⧸ K'.subgroupOf (GlobalTheory.HeckeCorr.heckeLevel K h⁻¹) →
        {u : K ⧸ K'.subgroupOf K // a⁻¹ * ((u.out : K) : Γ) ∈ GlobalTheory.HeckeCorr.heckeLevel K h⁻¹} :=
      fun q => ⟨((a' * Subgroup.inclusion hHK q.out : K) : K ⧸ K'.subgroupOf K), by
        rw [wd]
        simpa [a'] using q.out.2⟩
    apply Nat.card_eq_of_bijective F
    constructor
    · intro q₁ q₂ hq
      have hq' := congrArg Subtype.val hq
      simp only [F] at hq'
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at hq'
      rw [← QuotientGroup.out_eq' q₁, ← QuotientGroup.out_eq' q₂, QuotientGroup.eq, Subgroup.mem_subgroupOf]
      simpa [a', _root_.mul_assoc] using hq'
    · rintro ⟨u, hu⟩
      let x : GlobalTheory.HeckeCorr.heckeLevel K h⁻¹ := ⟨a⁻¹ * ((u.out : K) : Γ), hu⟩
      refine ⟨(x : GlobalTheory.HeckeCorr.heckeLevel K h⁻¹ ⧸ K'.subgroupOf (GlobalTheory.HeckeCorr.heckeLevel K h⁻¹)), ?_⟩
      apply Subtype.ext
      obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (K'.subgroupOf (GlobalTheory.HeckeCorr.heckeLevel K h⁻¹)) x
      simp only [F]
      rw [hk]
      conv_rhs => rw [← QuotientGroup.out_eq' u]
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have hk2 := Subgroup.mem_subgroupOf.mp k.2
      convert K'.inv_mem hk2 using 1
      simp [a', x, _root_.mul_assoc]
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro u _ hu
    apply hg
    rw [DoubleCoset.mem_doubleCoset]
    refine ⟨((u.out : K) : Γ), (u.out).2, h * ((((u.out : K) : Γ))⁻¹ * g * ((u.out : K) : Γ)) * (((u.out : K) : Γ))⁻¹,
      K.mul_mem hu (K.inv_mem (u.out).2), by group⟩

end Group

section Form

variable {p : ℕ} [Fact p.Prime] {G : HTGroup p} {v : InfinitePlace G.F}

private theorem toV_mul {β : G.Cˣ} (y y' : GlobalTheory.LKCx.grp G β) (z : Fin G.n → ℂ) :
    ((GlobalTheory.LKCx.toV G v β (y * y') : GL (Fin G.n) ℂ) : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z =
      (GlobalTheory.LKCx.toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ
        ((GlobalTheory.LKCx.toV G v β y' : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z) := by
  rw [map_mul, Units.val_mul, Matrix.mulVec_mulVec]

private theorem toV_inv {β : G.Cˣ} (y : GlobalTheory.LKCx.grp G β) (z : Fin G.n → ℂ) :
    (GlobalTheory.LKCx.toV G v β y⁻¹ : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ
      ((GlobalTheory.LKCx.toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z) = z := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one,
    Matrix.one_mulVec]

private theorem posV_ne {β : G.Cˣ} (z : GlobalTheory.LKCx.PosV G v β) : z.1 ≠ 0 := by
  intro h
  have := z.2
  rw [h] at this
  simp at this

private theorem fixL_div {β : G.Cˣ} {y y' : GlobalTheory.LKCx.grp G β} {z : Fin G.n → ℂ} (hz : z ≠ 0)
    (h : GlobalTheory.LKCx.FixL G v β y z) (h' : GlobalTheory.LKCx.FixL G v β y' z) : GlobalTheory.LKCx.FixL G v β (y⁻¹ * y') z := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨c', hc'⟩ := h'
  have key := toV_inv (v := v) y z
  rw [hc, Matrix.mulVec_smul] at key
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at key
    exact hz key.symm
  have hinv : (GlobalTheory.LKCx.toV G v β y⁻¹ : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z = c⁻¹ • z := by
    calc (GlobalTheory.LKCx.toV G v β y⁻¹ : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z
        = c⁻¹ • (c • (GlobalTheory.LKCx.toV G v β y⁻¹ : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z) := by
          rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
      _ = c⁻¹ • z := by rw [key]
  refine ⟨c⁻¹ * c', ?_⟩
  rw [toV_mul, hc', Matrix.mulVec_smul, hinv, smul_smul, mul_comm]

private theorem same_symm {β : G.Cˣ} {x : (AfP p ⊗[ℚ] G.C)ˣ} {t : (AfP p)ˣ} {hx : Triv G (AfP p) β x t}
    {Kf : Subgroup G.GAf} {K₂ : Subgroup (Gr G 1)} {a b : GlobalTheory.LKCx.Dat G v β}
    (h : GlobalTheory.LKCx.Same G v β x t hx Kf K₂ a b) : GlobalTheory.LKCx.Same G v β x t hx Kf K₂ b a := by
  obtain ⟨y, k, c, hk1, hk2, hc, h1, h2⟩ := h
  refine ⟨y⁻¹, k⁻¹, c⁻¹, Kf.inv_mem hk1, K₂.inv_mem hk2, inv_ne_zero hc, ?_, ?_⟩
  · have e : ((GlobalTheory.LKCx.toAfF G β x t hx y⁻¹, GlobalTheory.LKCx.toP1 G β y⁻¹) : G.GAf × Gr G 1) =
        (GlobalTheory.LKCx.toAfF G β x t hx y, GlobalTheory.LKCx.toP1 G β y)⁻¹ := by
      simp [map_inv]
    rw [h1, e]
    group
  · rw [h2, Matrix.mulVec_smul, toV_inv, smul_smul, inv_mul_cancel₀ hc, one_smul]

private theorem same_trans {β : G.Cˣ} {x : (AfP p ⊗[ℚ] G.C)ˣ} {t : (AfP p)ˣ} {hx : Triv G (AfP p) β x t}
    {Kf : Subgroup G.GAf} {K₂ : Subgroup (Gr G 1)} {a b d : GlobalTheory.LKCx.Dat G v β}
    (h : GlobalTheory.LKCx.Same G v β x t hx Kf K₂ a b) (h' : GlobalTheory.LKCx.Same G v β x t hx Kf K₂ b d) :
    GlobalTheory.LKCx.Same G v β x t hx Kf K₂ a d := by
  obtain ⟨y, k, c, hk1, hk2, hc, h1, h2⟩ := h
  obtain ⟨y', k', c', hk1', hk2', hc', h1', h2'⟩ := h'
  refine ⟨y' * y, k * k', c' * c, mul_mem hk1 hk1', mul_mem hk2 hk2', mul_ne_zero hc' hc, ?_, ?_⟩
  · rw [h1', h1, map_mul, map_mul]
    refine Prod.ext ?_ ?_ <;> simp only [Prod.fst_mul, Prod.snd_mul] <;> group
  · rw [h2', h2, Matrix.mulVec_smul, toV_mul, smul_smul]

private theorem same_of_eq {B : GlobalTheory.LKCx.Form G} {Kf : Subgroup G.GAf} {K₂ : Subgroup (Gr G 1)}
    {a a' : GlobalTheory.LKCx.Dat G v B.β}
    (h : (Quot.mk _ a : GlobalTheory.LKCx.Form.Pts v B Kf K₂) = Quot.mk _ a') :
    GlobalTheory.LKCx.Same G v B.β B.trivAf.choose B.trivAf.choose_spec.choose B.trivAf.choose_spec.choose_spec
      Kf K₂ a a' := by
  have hg := Quot.eqvGen_exact h
  clear h
  induction hg with
  | rel x y hxy => exact hxy
  | refl x => exact GlobalTheory.LKCx.same_refl _ _ _ _ _ _ _ _ x
  | symm x y _ ih => exact same_symm ih
  | trans x y z _ _ ih1 ih2 => exact same_trans ih1 ih2

private noncomputable def mv {B : GlobalTheory.LKCx.Form G} (b : GlobalTheory.LKCx.Dat G v B.β) (k : G.GAf) : GlobalTheory.LKCx.Dat G v B.β :=
  ((b.1.1 * k, b.1.2), b.2)

private theorem out_mk {B : GlobalTheory.LKCx.Form G} {Kf : Subgroup G.GAf} {K₂ : Subgroup (Gr G 1)}
    (b : GlobalTheory.LKCx.Form.Pts v B Kf K₂) : (Quot.mk _ (Quot.out b) : GlobalTheory.LKCx.Form.Pts v B Kf K₂) = b :=
  Quot.out_eq b

private theorem fibre_bij {B : GlobalTheory.LKCx.Form G} {K K' : Subgroup G.GAf} (hKK : K' ≤ K)
    (hst : ∀ (a : GlobalTheory.LKCx.Dat G v B.β) y, Sees B (K : Set G.GAf) a y → y = 1) :
    Function.Bijective (fun s : GlobalTheory.LKCx.Form.Pts v B K (KHT p G.m G.n 1 G.Fw) × (K ⧸ K'.subgroupOf K) =>
      (Quot.mk _ (mv (Quot.out s.1) ((s.2.out : K) : G.GAf)) : GlobalTheory.LKCx.Form.Pts v B K' (KHT p G.m G.n 1 G.Fw))) := by
  constructor
  · rintro ⟨s₁, u₁⟩ ⟨s₂, u₂⟩ heq
    obtain ⟨y, k, c, hk1, hk2, hc, h1, h2⟩ := same_of_eq heq
    have e1 : (Quot.out s₂).1.1 * ((u₂.out : K) : G.GAf) =
        B.toAf y * ((Quot.out s₁).1.1 * ((u₁.out : K) : G.GAf)) * k.1 := congrArg Prod.fst h1
    have e2 : (Quot.out s₂).1.2 = GlobalTheory.LKCx.toP1 G B.β y * (Quot.out s₁).1.2 * k.2 := congrArg Prod.snd h1
    have e3 : (Quot.out s₂).2.1 =
        c • (GlobalTheory.LKCx.toV G v B.β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ (Quot.out s₁).2.1 := h2
    have hs : s₁ = s₂ := by
      rw [← out_mk s₁, ← out_mk s₂]
      apply Quot.sound
      refine ⟨y, (((u₁.out : K) : G.GAf) * k.1 * ((u₂.out : K) : G.GAf)⁻¹, k.2), c,
        K.mul_mem (K.mul_mem (u₁.out).2 (hKK hk1)) (K.inv_mem (u₂.out).2), hk2, hc, ?_, e3⟩
      refine Prod.ext ?_ e2
      change (Quot.out s₂).1.1 = B.toAf y * (Quot.out s₁).1.1 *
        (((u₁.out : K) : G.GAf) * k.1 * ((u₂.out : K) : G.GAf)⁻¹)
      have : (Quot.out s₂).1.1 = (Quot.out s₂).1.1 * ((u₂.out : K) : G.GAf) * ((u₂.out : K) : G.GAf)⁻¹ := by
        group
      rw [this, e1]
      group
    refine Prod.ext hs ?_
    subst hs
    have hT : B.toAf y = (Quot.out s₁).1.1 * ((u₂.out : K) : G.GAf) * k.1⁻¹ *
        ((Quot.out s₁).1.1 * ((u₁.out : K) : G.GAf))⁻¹ := by
      rw [e1]
      group
    have hP : GlobalTheory.LKCx.toP1 G B.β y = (Quot.out s₁).1.2 * k.2⁻¹ * ((Quot.out s₁).1.2)⁻¹ := by
      calc GlobalTheory.LKCx.toP1 G B.β y
          = GlobalTheory.LKCx.toP1 G B.β y * (Quot.out s₁).1.2 * k.2 * k.2⁻¹ * ((Quot.out s₁).1.2)⁻¹ := by group
        _ = (Quot.out s₁).1.2 * k.2⁻¹ * ((Quot.out s₁).1.2)⁻¹ := by rw [← e2]
    have hc0 : c ≠ 0 := hc
    have hy : y = 1 := by
      refine hst (Quot.out s₁) y ⟨⟨c⁻¹, ?_⟩, ?_, ?_⟩
      · conv_rhs => rw [e3, smul_smul, inv_mul_cancel₀ hc0, one_smul]
      · rw [hT]
        have : (Quot.out s₁).1.1⁻¹ * ((Quot.out s₁).1.1 * ((u₂.out : K) : G.GAf) * k.1⁻¹ *
            ((Quot.out s₁).1.1 * ((u₁.out : K) : G.GAf))⁻¹) * (Quot.out s₁).1.1 =
            ((u₂.out : K) : G.GAf) * k.1⁻¹ * ((u₁.out : K) : G.GAf)⁻¹ := by group
        rw [this]
        exact K.mul_mem (K.mul_mem (u₂.out).2 (K.inv_mem (hKK hk1))) (K.inv_mem (u₁.out).2)
      · rw [hP]
        have : ((Quot.out s₁).1.2)⁻¹ * ((Quot.out s₁).1.2 * k.2⁻¹ * ((Quot.out s₁).1.2)⁻¹) *
            (Quot.out s₁).1.2 = k.2⁻¹ := by group
        rw [this]
        exact Subgroup.inv_mem _ hk2
    rw [hy, map_one] at e1
    have hk : ((u₁.out : K) : G.GAf)⁻¹ * ((u₂.out : K) : G.GAf) = k.1 := by
      have : ((u₂.out : K) : G.GAf) = ((Quot.out s₁).1.1)⁻¹ * ((Quot.out s₁).1.1 * ((u₂.out : K) : G.GAf)) := by
        group
      rw [this, e1]
      group
    rw [← QuotientGroup.out_eq' u₁, ← QuotientGroup.out_eq' u₂, QuotientGroup.eq,
      Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, hk]
    exact hk1
  · intro x
    obtain ⟨y, k, c, hk1, hk2, hc, h1, h2⟩ :=
      same_of_eq (out_mk (Quot.mk _ (Quot.out x) : GlobalTheory.LKCx.Form.Pts v B K (KHT p G.m G.n 1 G.Fw)))
    let u : K ⧸ K'.subgroupOf K := ((⟨k.1, hk1⟩ : K) : K ⧸ K'.subgroupOf K)
    have hr := out_rel (B := K') (⟨k.1, hk1⟩ : K)
    refine ⟨(Quot.mk _ (Quot.out x), u), ?_⟩
    dsimp only
    conv_rhs => rw [← out_mk x]
    apply Quot.sound
    refine ⟨y, (((u.out : K) : G.GAf)⁻¹ * k.1, k.2), c, ?_, hk2, hc, ?_, h2⟩
    · have := K'.inv_mem hr
      rw [mul_inv_rev, inv_inv] at this
      exact this
    · have e1 : (Quot.out x).1.1 = B.toAf y *
          (Quot.out (Quot.mk _ (Quot.out x) : GlobalTheory.LKCx.Form.Pts v B K (KHT p G.m G.n 1 G.Fw))).1.1 * k.1 :=
        congrArg Prod.fst h1
      refine Prod.ext ?_ ?_
      swap
      · have e2 := congrArg Prod.snd h1
        exact e2
      change (Quot.out x).1.1 = B.toAf y *
        ((Quot.out (Quot.mk _ (Quot.out x) : GlobalTheory.LKCx.Form.Pts v B K (KHT p G.m G.n 1 G.Fw))).1.1 *
          ((u.out : K) : G.GAf)) * (((u.out : K) : G.GAf)⁻¹ * k.1)
      rw [e1]
      group

private noncomputable def wt (v : InfinitePlace G.F) (c : G.F[X] → ℂ → ℂ) (S : Set G.GAf) (B : GlobalTheory.LKCx.Form G)
    (a : GlobalTheory.LKCx.Dat G v B.β) : ℂ :=
  ∑ᶠ y : GlobalTheory.LKCx.grp G B.β, if Sees B S a y then
    c (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) (GlobalTheory.RootSumWeights.eigL G v B.β y a.2.1) else 0

private theorem wt_congr (hE : EigSame) (c : G.F[X] → ℂ → ℂ) (B : GlobalTheory.LKCx.Form G) (K : Subgroup G.GAf)
    (S : Set G.GAf) (hS : ∀ u ∈ K, ∀ g, u⁻¹ * g * u ∈ S ↔ g ∈ S) {a a' : GlobalTheory.LKCx.Dat G v B.β}
    (h : (Quot.mk _ a : GlobalTheory.LKCx.Form.Pts v B K (KHT p G.m G.n 1 G.Fw)) = Quot.mk _ a') :
    wt v c S B a = wt v c S B a' := by
  obtain ⟨E, -, hEy⟩ := hE p G v c B K S hS a a' h
  have h1 := finsum_comp_equiv E (f := fun y : GlobalTheory.LKCx.grp G B.β => if Sees B S a' y then
    c (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) (GlobalTheory.RootSumWeights.eigL G v B.β y a'.2.1) else 0)
  refine Eq.trans ?_ h1
  unfold wt
  refine finsum_congr fun y => ?_
  by_cases hy : Sees B S a y
  · rw [if_pos hy, if_pos ((hEy y).1.1 hy), ((hEy y).2 hy).1, ((hEy y).2 hy).2]
  · rw [if_neg hy, if_neg (fun h' => hy ((hEy y).1.2 h'))]

private theorem term_eq (c : G.F[X] → ℂ → ℂ) (K : Subgroup G.GAf) (S : Set G.GAf) (B : GlobalTheory.LKCx.Form G)
    (b : GlobalTheory.LKCx.Dat G v B.β) (hK : ∀ y, Sees B (K : Set G.GAf) b y → y = 1) :
    ((Nat.card (GlobalTheory.LKCx.Form.Stab v B K (KHT p G.m G.n 1 G.Fw) b) : ℕ) : ℂ)⁻¹ *
      ∑ᶠ y : GlobalTheory.LKCx.grp G B.β, (if GlobalTheory.LKCx.FixL G v B.β y b.2.1 then
        (S.indicator (1 : G.GAf → ℂ)) (b.1.1⁻¹ * B.toAf y * b.1.1) *
          (((KHT p G.m G.n 1 G.Fw) : Set (Gr G 1)).indicator (1 : Gr G 1 → ℂ))
            (b.1.2⁻¹ * GlobalTheory.LKCx.toP1 G B.β y * b.1.2) *
          c (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) (GlobalTheory.RootSumWeights.eigL G v B.β y b.2.1) else 0) =
      wt v c S B b := by
  have hcard : Nat.card (GlobalTheory.LKCx.Form.Stab v B K (KHT p G.m G.n 1 G.Fw) b) = 1 := by
    have hu : Unique (GlobalTheory.LKCx.Form.Stab v B K (KHT p G.m G.n 1 G.Fw) b) :=
      { default := GlobalTheory.LKCx.Stab.one G v B.β _ _ _ K _ b
        uniq := fun s => Subtype.ext (hK s.1 ⟨s.2.2.2, s.2.1, s.2.2.1⟩) }
    exact Nat.card_unique
  rw [hcard, Nat.cast_one, inv_one, _root_.one_mul]
  unfold wt
  refine finsum_congr fun y => ?_
  by_cases h1 : GlobalTheory.LKCx.FixL G v B.β y b.2.1
  · rw [if_pos h1]
    by_cases h2 : b.1.1⁻¹ * B.toAf y * b.1.1 ∈ S
    · by_cases h3 : b.1.2⁻¹ * GlobalTheory.LKCx.toP1 G B.β y * b.1.2 ∈ KHT p G.m G.n 1 G.Fw
      · rw [if_pos (show Sees B S b y from ⟨h1, h2, h3⟩), Set.indicator_of_mem h2,
          Set.indicator_of_mem (show _ ∈ ((KHT p G.m G.n 1 G.Fw) : Set (Gr G 1)) from h3)]
        simp
      · rw [if_neg (fun h => h3 h.2.2),
          Set.indicator_of_notMem (show _ ∉ ((KHT p G.m G.n 1 G.Fw) : Set (Gr G 1)) from h3)]
        simp
    · rw [if_neg (fun h => h2 h.2.1), Set.indicator_of_notMem h2]
      simp
  · rw [if_neg h1, if_neg (fun h => h1 h.1)]

private theorem sees_unique {B : GlobalTheory.LKCx.Form G} {K : Subgroup G.GAf} {h : G.GAf} (a : GlobalTheory.LKCx.Dat G v B.β)
    (hst : ∀ y, Sees B (K : Set G.GAf) a y → y = 1) {y y' : GlobalTheory.LKCx.grp G B.β}
    (hy : Sees B {g | h * g ∈ K} a y) (hy' : Sees B {g | h * g ∈ K} a y') : y = y' := by
  have h1 : y⁻¹ * y' = 1 := by
    refine hst _ ⟨fixL_div (posV_ne a.2) hy.1 hy'.1, ?_, ?_⟩
    · have e : a.1.1⁻¹ * B.toAf (y⁻¹ * y') * a.1.1 =
          (h * (a.1.1⁻¹ * B.toAf y * a.1.1))⁻¹ * (h * (a.1.1⁻¹ * B.toAf y' * a.1.1)) := by
        rw [map_mul, map_inv]
        group
      rw [e]
      exact K.mul_mem (K.inv_mem hy.2.1) hy'.2.1
    · have e : a.1.2⁻¹ * GlobalTheory.LKCx.toP1 G B.β (y⁻¹ * y') * a.1.2 =
          (a.1.2⁻¹ * GlobalTheory.LKCx.toP1 G B.β y * a.1.2)⁻¹ * (a.1.2⁻¹ * GlobalTheory.LKCx.toP1 G B.β y' * a.1.2) := by
        rw [map_mul, map_inv]
        group
      rw [e]
      exact (KHT p G.m G.n 1 G.Fw).mul_mem ((KHT p G.m G.n 1 G.Fw).inv_mem hy.2.2) hy'.2.2
  exact inv_mul_eq_one.1 h1

private theorem point_sum {B : GlobalTheory.LKCx.Form G} {K K' : Subgroup G.GAf} {h : G.GAf}
    (hle : K' ≤ GlobalTheory.HeckeCorr.heckeLevel K h⁻¹) [Fintype (K ⧸ K'.subgroupOf K)]
    (hst : ∀ (a : GlobalTheory.LKCx.Dat G v B.β) y, Sees B (K : Set G.GAf) a y → y = 1)
    (c : G.F[X] → ℂ → ℂ) (b : GlobalTheory.LKCx.Dat G v B.β) :
    ∑ u : K ⧸ K'.subgroupOf K, wt v c {g | h * g ∈ K} B (mv b ((u.out : K) : G.GAf)) =
      (K'.relIndex (GlobalTheory.HeckeCorr.heckeLevel K h⁻¹) : ℂ) *
        wt v c (DoubleCoset.doubleCoset h⁻¹ (K : Set G.GAf) (K : Set G.GAf)) B b := by
  unfold wt
  rw [sum_finsum_comm _ _ ?_, mul_finsum]
  · refine finsum_congr fun y => ?_
    simp only [Sees, mv]
    by_cases hA : LKCx.FixL G v B.β y b.2.1
    · by_cases hP : b.1.2⁻¹ * (LKCx.toP1 G B.β) y * b.1.2 ∈ KHT p G.m G.n 1 G.Fw
      · have hconj : ∀ k : G.GAf, (b.1.1 * k)⁻¹ * B.toAf y * (b.1.1 * k) =
            k⁻¹ * (b.1.1⁻¹ * B.toAf y * b.1.1) * k := fun k => by group
        simp only [hA, hP, true_and, and_true, hconj, Set.mem_setOf_eq]
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
          count_eq hle]
        split_ifs <;> simp
      · simp [hP]
    · simp [hA]
  · intro u _
    unfold Function.HasFiniteSupport
    refine Set.Subsingleton.finite ?_
    intro y hy y' hy'
    have hs : Sees B {g | h * g ∈ K} (mv b ((u.out : K) : G.GAf)) y := by
      by_contra hn
      exact hy (if_neg hn)
    have hs' : Sees B {g | h * g ∈ K} (mv b ((u.out : K) : G.GAf)) y' := by
      by_contra hn
      exact hy' (if_neg hn)
    exact sees_unique _ (hst _) hs hs'

private theorem form_eq (hE : EigSame) (c : G.F[X] → ℂ → ℂ) {K K' : Subgroup G.GAf} {h : G.GAf}
    (hle : K' ≤ GlobalTheory.HeckeCorr.heckeLevel K h⁻¹) (hfin : K'.relIndex K ≠ 0) (B : GlobalTheory.LKCx.Form G)
    (hst : ∀ (a : GlobalTheory.LKCx.Dat G v B.β) y, Sees B (K : Set G.GAf) a y → y = 1)
    (hF : {x : GlobalTheory.LKCx.Form.Pts v B K' (KHT p G.m G.n 1 G.Fw) | ∃ y, Sees B {g | h * g ∈ K} (Quot.out x) y}.Finite) :
    GlobalTheory.RootSumWeights.cxSumM G v c B K' ({g | h * g ∈ K}.indicator 1) (KHT p G.m G.n 1 G.Fw)
                 (((KHT p G.m G.n 1 G.Fw) : Set (Gr G 1)).indicator 1) =
      (K'.relIndex (GlobalTheory.HeckeCorr.heckeLevel K h⁻¹) : ℂ) *
        GlobalTheory.RootSumWeights.cxSumM G v c B K (Formalism.UG.dosetInd ℂ K h⁻¹) (KHT p G.m G.n 1 G.Fw)
          (((KHT p G.m G.n 1 G.Fw) : Set (Gr G 1)).indicator 1) := by
  have hK'K : K' ≤ K := hle.trans (GlobalTheory.HeckeCorr.heckeLevel_le _ _)
  have hst' : ∀ (a : GlobalTheory.LKCx.Dat G v B.β) y, Sees B (K' : Set G.GAf) a y → y = 1 :=
    fun a y hs => hst a y ⟨hs.1, hK'K hs.2.1, hs.2.2⟩
  have hS : ∀ u ∈ K', ∀ g, u⁻¹ * g * u ∈ {g : G.GAf | h * g ∈ K} ↔ g ∈ {g : G.GAf | h * g ∈ K} := by
    intro u hu g
    obtain ⟨hu1, hu2⟩ := mem_hl.1 (hle hu)
    simp only [Set.mem_setOf_eq]
    constructor
    · intro hx
      have e : h * g = (h * u * h⁻¹) * (h * (u⁻¹ * g * u)) * u⁻¹ := by group
      rw [e]
      exact mul_mem (mul_mem hu2 hx) (inv_mem hu1)
    · intro hx
      have e : h * (u⁻¹ * g * u) = (h * u * h⁻¹)⁻¹ * (h * g) * u := by group
      rw [e]
      exact mul_mem (mul_mem (inv_mem hu2) hx) hu1
  haveI : (K'.subgroupOf K).FiniteIndex := ⟨hfin⟩
  haveI := Fintype.ofFinite (K ⧸ K'.subgroupOf K)
  let e := Equiv.ofBijective _ (fibre_bij (v := v) (B := B) hK'K hst)
  let F : GlobalTheory.LKCx.Form.Pts v B K' (KHT p G.m G.n 1 G.Fw) → ℂ :=
    fun q => wt v c {g | h * g ∈ K} B (Quot.out q)
  have hFs : Function.HasFiniteSupport F := by
    unfold Function.HasFiniteSupport
    refine hF.subset fun q hq => ?_
    by_contra hn
    apply hq
    refine finsum_eq_zero_of_forall_eq_zero fun y => ?_
    exact if_neg fun hy => hn ⟨y, hy⟩
  calc _ = ∑ᶠ q, F q := by
        unfold GlobalTheory.RootSumWeights.cxSumM GlobalTheory.RootSumWeights.cxSumAtM
        exact finsum_congr fun q => term_eq c K' _ B _ (hst' _)
    _ = ∑ᶠ s, F (e s) := (finsum_comp_equiv e).symm
    _ = ∑ᶠ (a : GlobalTheory.LKCx.Form.Pts v B K (KHT p G.m G.n 1 G.Fw)) (u : K ⧸ K'.subgroupOf K), F (e (a, u)) := by
        refine finsum_curry _ ?_
        unfold Function.HasFiniteSupport at hFs ⊢
        exact hFs.preimage e.injective.injOn
    _ = ∑ᶠ (a : GlobalTheory.LKCx.Form.Pts v B K (KHT p G.m G.n 1 G.Fw)),
          (K'.relIndex (GlobalTheory.HeckeCorr.heckeLevel K h⁻¹) : ℂ) *
            wt v c (DoubleCoset.doubleCoset h⁻¹ (K : Set G.GAf) (K : Set G.GAf)) B (Quot.out a) := by
        refine finsum_congr fun a => ?_
        rw [finsum_eq_sum_of_fintype, ← point_sum hle hst c]
        refine Finset.sum_congr rfl fun u _ => ?_
        exact wt_congr hE c B K' _ hS (out_mk _)
    _ = _ := by
        rw [← mul_finsum]
        unfold GlobalTheory.RootSumWeights.cxSumM GlobalTheory.RootSumWeights.cxSumAtM Formalism.UG.dosetInd
        congr 1
        exact finsum_congr fun q => (term_eq c K _ B _ (hst _)).symm

end Form

end UpperTheory.Gal.W2.levelStructure

open UpperTheory.Gal.W2.levelStructure in
theorem UpperTheory.Gal.W2.levelChange_of :
    UpperTheory.Gal.W2.EigSame → UpperTheory.Gal.W2.LevelChange := by
  intro hE p _ G v c K K' h hle hfin hst hF
  have h2 := smul_finsum ((K'.relIndex (GlobalTheory.HeckeCorr.heckeLevel K h⁻¹) : ℕ) : ℂ)
    (fun q : GlobalTheory.LKCx.FCls G => GlobalTheory.RootSumWeights.cxSumM G v c (Quot.out q) K (Formalism.UG.dosetInd ℂ K h⁻¹)
      (KHT p G.m G.n 1 G.Fw) (((KHT p G.m G.n 1 G.Fw) : Set (Gr G 1)).indicator 1))
  simp only [smul_eq_mul] at h2
  unfold GlobalTheory.RootSumWeights.cxTotalM
  rw [h2]
  refine finsum_congr fun q => ?_
  exact form_eq hE c hle hfin (Quot.out q) (hst _)
    (hF.preimage (f := Sigma.mk q) sigma_mk_injective.injOn)
