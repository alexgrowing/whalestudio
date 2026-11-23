import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExtVPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi

section DivPull

variable {X Y : Scheme.{0}}

theorem mem_pull_iff {M : LB X} (f : Y ⟶ X) (j : PUnit → M.ι) (y : Y) :
    y ∈ (M.pull f).U j ↔ f y ∈ M.U (j ⟨⟩) := ⟨fun h => Set.mem_iInter.1 h ⟨⟩, fun h => Set.mem_iInter.2 fun ⟨⟩ => h⟩

theorem le_div_left {L M : LB X} (f : Y ⟶ X) (J : PUnit → M.ι × L.ι) :
    ((LB.div M L).pull f).U J ≤ (M.pull f).U (fun _ => (J ⟨⟩).1) := fun y hy => Set.mem_iInter.2 fun _ => And.left (Set.mem_iInter.1 hy ⟨⟩)

theorem le_div_right {L M : LB X} (f : Y ⟶ X) (J : PUnit → M.ι × L.ι) :
    ((LB.div M L).pull f).U J ≤ (L.pull f).U (fun _ => (J ⟨⟩).2) := fun y hy => Set.mem_iInter.2 fun _ => And.right (Set.mem_iInter.1 hy ⟨⟩)

def divPullGen {L M : LB X} (f : Y ⟶ X) (a : LB.Gen (L.pull f)) (b : LB.Gen (M.pull f)) :
    LB.Gen ((LB.div M L).pull f) where
  s := fun J => res (le_div_left f J) (b.s (fun _ => (J ⟨⟩).1)) * (res (le_div_right f J) (a.s (fun _ => (J ⟨⟩).2)))⁻¹

theorem gm_pullG' {Z : Scheme.{0}} {M : LB X} (f : Y ⟶ X) (g : Z ⟶ Y) (z : Z) (j j' : PUnit → M.ι)
    (hz : g z ∈ (M.pull f).U j ⊓ (M.pull f).U j') :
    gm g z _ ((M.pull f).g j j') = gm (g ≫ f) z (M.U (j ⟨⟩) ⊓ M.U (j' ⟨⟩)) (M.g (j ⟨⟩) (j' ⟨⟩)) := by
  have h1 : f (g z) ∈ M.U (j ⟨⟩) ⊓ M.U (j' ⟨⟩) :=
    ⟨(mem_pull_iff f j _).1 (Opens.mem_inf.1 hz).1, (mem_pull_iff f j' _).1 (Opens.mem_inf.1 hz).2⟩
  show gm g z _ (∏ _k : PUnit, _) = _
  simp only [zpow_one]
  refine (congrArg (gm g z _) (Fintype.prod_unique _)).trans ?_
  exact (gm_res g z _ hz _).trans (gm_pull g f z _ h1 _)

private theorem gm_res_mul_inv_res (f : Y ⟶ X) (y : Y) {W U₁ U₂ : X.Opens} (h₁ : W ≤ U₁) (h₂ : W ≤ U₂)
    (hy : f y ∈ W) (a : Γ(X, U₁)ˣ) (b : Γ(X, U₂)ˣ) :
    gm f y W (res h₁ a * (res h₂ b)⁻¹) = gm f y U₁ a * (gm f y U₂ b)⁻¹ := by
  rw [map_mul, map_inv, gm_res f y h₁ hy, gm_res f y h₂ hy]

theorem gm_div_pull_g {L M : LB X} (f : Y ⟶ X) (y : Y) (J J' : PUnit → M.ι × L.ι)
    (hy : y ∈ ((LB.div M L).pull f).U J ⊓ ((LB.div M L).pull f).U J') :
    gm (𝟙 Y) y _ (((LB.div M L).pull f).g J J') =
      gm f y (M.U (J ⟨⟩).1 ⊓ M.U (J' ⟨⟩).1) (M.g (J ⟨⟩).1 (J' ⟨⟩).1) *
        (gm f y (L.U (J ⟨⟩).2 ⊓ L.U (J' ⟨⟩).2) (L.g (J ⟨⟩).2 (J' ⟨⟩).2))⁻¹ := by
  have hy' := Opens.mem_inf.1 hy
  have h1 : f y ∈ (LB.div M L).U (J ⟨⟩) ⊓ (LB.div M L).U (J' ⟨⟩) :=
    Opens.mem_inf.2 ⟨(mem_pull_iff (M := LB.div M L) f J y).1 hy'.1,
      (mem_pull_iff (M := LB.div M L) f J' y).1 hy'.2⟩
  show gm (𝟙 Y) y _ (∏ _k : PUnit, _) = _
  simp only [zpow_one]
  refine (congrArg (gm (𝟙 Y) y _) (Fintype.prod_unique _)).trans ?_
  refine (gm_res (𝟙 Y) y _ hy _).trans ((gm_pull (𝟙 Y) f y _ h1 _).trans ?_)
  rw [Category.id_comp]
  exact gm_res_mul_inv_res f y _ _ h1 _ _

private theorem pullU_res_eq_res_preimage_mono {A B : Scheme.{0}} (g : A ⟶ B) {U V : B.Opens} (h : V ≤ U) (u : Γ(B, U)ˣ) :
    pullU g V (res h u) = res (g.preimage_mono h) (pullU g U u) := by
  apply Units.ext
  have := congrArg (fun φ => φ.hom u.val) (g.naturality (homOfLE h).op)
  simpa [pullU, res] using this

private theorem res_res_eq_res_trans' {Z : Scheme.{0}} {U V W : Z.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (a : Γ(Z, U)ˣ) :
    res h₂ (res h₁ a) = res (h₂.trans h₁) a := by
  apply Units.ext
  first
    | (simp [res]; done)
    | (simp only [res, Units.coe_map, MonoidHom.coe_coe]
       rw [← CommRingCat.comp_apply, ← Functor.map_comp]
       rfl)

private theorem pull_U_inf_le_preimage_inf {P : LB X} (f : Y ⟶ X) (j j' : PUnit → P.ι) :
    (P.pull f).U j ⊓ (P.pull f).U j' ≤ f ⁻¹ᵁ (P.U (j ⟨⟩) ⊓ P.U (j' ⟨⟩)) :=
  fun y hy => show f y ∈ P.U (j ⟨⟩) ⊓ P.U (j' ⟨⟩) from
    Opens.mem_inf.2 ⟨(mem_pull_iff f j y).1 (Opens.mem_inf.1 hy).1,
      (mem_pull_iff f j' y).1 (Opens.mem_inf.1 hy).2⟩

private theorem pull_g_eq_res_pullU_g {P : LB X} (f : Y ⟶ X) (j j' : PUnit → P.ι)
    (hle : (P.pull f).U j ⊓ (P.pull f).U j' ≤ f ⁻¹ᵁ (P.U (j ⟨⟩) ⊓ P.U (j' ⟨⟩))) :
    (P.pull f).g j j' = res hle (pullU f _ (P.g (j ⟨⟩) (j' ⟨⟩))) := by
  show (∏ _k : PUnit, _) = _
  simp only [zpow_one]
  exact Fintype.prod_unique _

private theorem res_pullU_res_mul_inv_res (f : Y ⟶ X) {W U₁ U₂ : X.Opens} (h₁ : W ≤ U₁) (h₂ : W ≤ U₂)
    {V : Y.Opens} (h0 : V ≤ f ⁻¹ᵁ W) (k₁ : V ≤ f ⁻¹ᵁ U₁) (k₂ : V ≤ f ⁻¹ᵁ U₂)
    (a : Γ(X, U₁)ˣ) (b : Γ(X, U₂)ˣ) :
    res h0 (pullU f W (res h₁ a * (res h₂ b)⁻¹)) = res k₁ (pullU f U₁ a) * (res k₂ (pullU f U₂ b))⁻¹ := by
  rw [map_mul, map_inv, pullU_res_eq_res_preimage_mono, pullU_res_eq_res_preimage_mono, map_mul, map_inv, res_res_eq_res_trans', res_res_eq_res_trans']

theorem divPullGen_isGen {L M : LB X} (f : Y ⟶ X) (a : LB.Gen (L.pull f)) (b : LB.Gen (M.pull f)) (ha : a.IsGen)
    (hb : b.IsGen) : (divPullGen f a b).IsGen := by
  intro J J'
  have hVM : ((LB.div M L).pull f).U J ⊓ ((LB.div M L).pull f).U J' ≤
      (M.pull f).U (fun _ => (J ⟨⟩).1) ⊓ (M.pull f).U (fun _ => (J' ⟨⟩).1) :=
    inf_le_inf (le_div_left f J) (le_div_left f J')
  have hVL : ((LB.div M L).pull f).U J ⊓ ((LB.div M L).pull f).U J' ≤
      (L.pull f).U (fun _ => (J ⟨⟩).2) ⊓ (L.pull f).U (fun _ => (J' ⟨⟩).2) :=
    inf_le_inf (le_div_right f J) (le_div_right f J')
  have hb' := congrArg (res hVM) (hb (fun _ => (J ⟨⟩).1) (fun _ => (J' ⟨⟩).1))
  have ha' := congrArg (res hVL) (ha (fun _ => (J ⟨⟩).2) (fun _ => (J' ⟨⟩).2))
  rw [map_mul, res_res_eq_res_trans', res_res_eq_res_trans'] at hb' ha'
  have hG : ((LB.div M L).pull f).g J J' =
      res hVM ((M.pull f).g (fun _ => (J ⟨⟩).1) (fun _ => (J' ⟨⟩).1)) *
        (res hVL ((L.pull f).g (fun _ => (J ⟨⟩).2) (fun _ => (J' ⟨⟩).2)))⁻¹ := by
    rw [pull_g_eq_res_pullU_g (P := LB.div M L) f J J' (pull_U_inf_le_preimage_inf (P := LB.div M L) f J J'),
      pull_g_eq_res_pullU_g (P := M) f _ _ (pull_U_inf_le_preimage_inf (P := M) f _ _),
      pull_g_eq_res_pullU_g (P := L) f _ _ (pull_U_inf_le_preimage_inf (P := L) f _ _), res_res_eq_res_trans', res_res_eq_res_trans']
    exact res_pullU_res_mul_inv_res f _ _ _ _ _ _ _
  show res _ (res _ (b.s _) * (res _ (a.s _))⁻¹) =
    _ * res _ (res _ (b.s _) * (res _ (a.s _))⁻¹)
  rw [hG, map_mul, map_inv, map_mul, map_inv, res_res_eq_res_trans', res_res_eq_res_trans', res_res_eq_res_trans', res_res_eq_res_trans',
    hb', ha']
  first
    | (simp only [mul_inv_rev]; ac_rfl)
    | (simp [mul_comm, mul_assoc, mul_left_comm]; done)

end DivPull

section GenericGen

variable {X A K₀ : Scheme.{0}} {L₁ : LB X} {L₂ : LB X} {L₀ : LB K₀}

theorem exists_gen_ratio {Xp : Scheme.{0}} {L₂' : LB Xp} (ψ : X ⟶ Xp) (F₁ : K₀ ⟶ X) (F₂ : K₀ ⟶ Xp)
    (ι : A ⟶ K₀) (jA : A ⟶ X) (h₁ : ι ≫ F₁ = jA) (h₂ : ι ≫ F₂ = jA ≫ ψ) (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB)
    (hL₂ : L₂'.IsLB)
    (w₁ : LB.Iso L₀ (L₁.pull F₁)) (w₂ : LB.Iso L₀ (L₂'.pull F₂)) (p₁ : PGen w₁) (p₂ : PGen w₂) :
    ∃ r : LB.Gen ((LB.div (L₂'.pull ψ) L₁).pull jA),
      ∀ (Z : Scheme.{0}) (f : Z ⟶ A) (z : Z) (j : L₂'.ι) (k : L₁.ι) (k₂ : L₀.ι), ψ (jA (f z)) ∈ L₂'.U j →
        jA (f z) ∈ L₁.U k → ι (f z) ∈ L₀.U k₂ →
        gm f z _ (r.s (fun _ => ((fun _ => j), k))) = gw w₂ (f ≫ ι) z j k₂ * (gw w₁ (f ≫ ι) z k k₂)⁻¹ := by
  have pt₁ : ∀ y, F₁ (ι y) = jA y := fun y => congrArg (fun g => g y) h₁
  have pt₂ : ∀ y, F₂ (ι y) = ψ (jA y) := fun y => congrArg (fun g => g y) h₂
  have glue : ∀ (J : PUnit → (PUnit → L₂'.ι) × L₁.ι), ∃ s : Γ(A, ((LB.div (L₂'.pull ψ) L₁).pull jA).U J)ˣ,
      ∀ (Z : Scheme.{0}) (f : Z ⟶ A) (z : Z) (k₂ : L₀.ι), f z ∈ ((LB.div (L₂'.pull ψ) L₁).pull jA).U J →
        ι (f z) ∈ L₀.U k₂ →
        gm f z _ s = gw w₂ (f ≫ ι) z ((J ⟨⟩).1 ⟨⟩) k₂ * (gw w₁ (f ≫ ι) z (J ⟨⟩).2 k₂)⁻¹ := by
    intro J
    set Vo := ((LB.div (L₂'.pull ψ) L₁).pull jA).U J
    have memV : ∀ y, y ∈ Vo ↔ ψ (jA y) ∈ L₂'.U ((J ⟨⟩).1 ⟨⟩) ∧ jA y ∈ L₁.U (J ⟨⟩).2 := fun y => by
      rw [mem_pull_iff (M := LB.div (L₂'.pull ψ) L₁) jA J y]
      exact and_congr (mem_pull_iff ψ _ (jA y)) Iff.rfl
    let W : L₀.ι → A.Opens := fun k₂ => Vo ⊓ ι ⁻¹ᵁ L₀.U k₂
    have l₀ : ∀ k₂, W k₂ ≤ Vo := fun _ => inf_le_left
    have l₁ : ∀ k₂, W k₂ ≤ ι ⁻¹ᵁ ((L₁.pull F₁).U (fun _ => (J ⟨⟩).2) ⊓ L₀.U k₂) := fun k₂ y hy =>
      ⟨(mem_pull_iff F₁ _ (ι y)).2 (by rw [pt₁]; exact ((memV y).1 hy.1).2), hy.2⟩
    have l₂ : ∀ k₂, W k₂ ≤ ι ⁻¹ᵁ ((L₂'.pull F₂).U (fun _ => (J ⟨⟩).1 ⟨⟩) ⊓ L₀.U k₂) := fun k₂ y hy =>
      ⟨(mem_pull_iff F₂ _ (ι y)).2 (by rw [pt₂]; exact ((memV y).1 hy.1).1), hy.2⟩
    let u : ∀ k₂, Γ(A, W k₂)ˣ := fun k₂ =>
      res (l₂ k₂) (pullU ι _ (w₂.s (fun _ => (J ⟨⟩).1 ⟨⟩, k₂))) *
        (res (l₁ k₂) (pullU ι _ (w₁.s (fun _ => (J ⟨⟩).2, k₂))))⁻¹
    have hu : ∀ (Z : Scheme.{0}) (f : Z ⟶ A) (z : Z) (k₂ : L₀.ι), f z ∈ W k₂ →
        gm f z (W k₂) (u k₂) = gw w₂ (f ≫ ι) z ((J ⟨⟩).1 ⟨⟩) k₂ * (gw w₁ (f ≫ ι) z (J ⟨⟩).2 k₂)⁻¹ := by
      intro Z f z k₂ hz
      show gm f z (W k₂) (res _ _ * (res _ _)⁻¹) = _
      rw [map_mul, map_inv, gm_res f z _ hz, gm_res f z _ hz]
      exact congrArg₂ (fun a b => a * b⁻¹) (gm_pull f ι z _ (show ι (f z) ∈ _ from l₂ k₂ hz) _)
        (gm_pull f ι z _ (show ι (f z) ∈ _ from l₁ k₂ hz) _)
    obtain ⟨s, hs⟩ := glue_unit Vo W l₀ (fun y hy => by
        obtain ⟨k₂, hk₂⟩ := exists_chart hL₀ (ι y)
        exact Opens.mem_iSup.2 ⟨k₂, hy, hk₂⟩) u (fun k₂ k₂' y hy => by
        rw [hu A (𝟙 A) y k₂ hy.1, hu A (𝟙 A) y k₂' hy.2]
        have hj : F₂ ((𝟙 A ≫ ι) y) ∈ L₂'.U ((J ⟨⟩).1 ⟨⟩) := by
          show F₂ (ι y) ∈ _; rw [pt₂]; exact ((memV y).1 hy.1.1).1
        have hk : F₁ ((𝟙 A ≫ ι) y) ∈ L₁.U (J ⟨⟩).2 := by
          show F₁ (ι y) ∈ _; rw [pt₁]; exact ((memV y).1 hy.1.1).2
        have a₂ := p₂ A (𝟙 A ≫ ι) y _ _ k₂ k₂' hj hj hy.1.2 hy.2.2
        have a₁ := p₁ A (𝟙 A ≫ ι) y _ _ k₂ k₂' hk hk hy.1.2 hy.2.2
        rw [gm_self hL₂ _ y hj, one_mul] at a₂
        rw [gm_self hL₁ _ y hk, one_mul] at a₁
        rw [a₁, a₂]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel)
    refine ⟨s, fun Z f z k₂ hz hk => ?_⟩
    have hw : f z ∈ W k₂ := ⟨hz, hk⟩
    rw [← hu Z f z k₂ hw, ← hs k₂, gm_res f z _ hw]
  choose s hs using glue
  exact ⟨⟨s⟩, fun Z f z j k k₂ hj hk hk₂ => hs _ Z f z k₂ ((mem_pull_iff (M := LB.div (L₂'.pull ψ) L₁) jA _ _).2
    ⟨(mem_pull_iff ψ _ _).2 hj, hk⟩) hk₂⟩

theorem gen_ratio_isGen {Xp : Scheme.{0}} {L₂' : LB Xp} (ψ : X ⟶ Xp) (F₁ : K₀ ⟶ X) (F₂ : K₀ ⟶ Xp)
    (ι : A ⟶ K₀) (jA : A ⟶ X) (h₁ : ι ≫ F₁ = jA) (h₂ : ι ≫ F₂ = jA ≫ ψ) (hL₀ : L₀.IsLB)
    (w₁ : LB.Iso L₀ (L₁.pull F₁)) (w₂ : LB.Iso L₀ (L₂'.pull F₂)) (p₁ : PGen w₁) (p₂ : PGen w₂)
    (r : LB.Gen ((LB.div (L₂'.pull ψ) L₁).pull jA))
    (hr : ∀ (Z : Scheme.{0}) (f : Z ⟶ A) (z : Z) (j : L₂'.ι) (k : L₁.ι) (k₂ : L₀.ι), ψ (jA (f z)) ∈ L₂'.U j →
        jA (f z) ∈ L₁.U k → ι (f z) ∈ L₀.U k₂ →
        gm f z _ (r.s (fun _ => ((fun _ => j), k))) = gw w₂ (f ≫ ι) z j k₂ * (gw w₁ (f ≫ ι) z k k₂)⁻¹) :
    r.IsGen := by
  have pt₁ : ∀ y, F₁ (ι y) = jA y := fun y => congrArg (fun g => g y) h₁
  have pt₂ : ∀ y, F₂ (ι y) = ψ (jA y) := fun y => congrArg (fun g => g y) h₂
  intro J J'
  apply unit_ext
  intro y hy
  have m₁ := (mem_pull_iff (M := LB.div (L₂'.pull ψ) L₁) jA J y).1 hy.1
  have m₂ := (mem_pull_iff (M := LB.div (L₂'.pull ψ) L₁) jA J' y).1 hy.2
  have a1 : ψ (jA y) ∈ L₂'.U ((J ⟨⟩).1 ⟨⟩) := (mem_pull_iff ψ _ (jA y)).1 m₁.1
  have a2 : ψ (jA y) ∈ L₂'.U ((J' ⟨⟩).1 ⟨⟩) := (mem_pull_iff ψ _ (jA y)).1 m₂.1
  obtain ⟨k₂, hk₂⟩ := exists_chart hL₀ (ι y)
  have v₁ : gm (𝟙 A) y (((LB.div (L₂'.pull ψ) L₁).pull jA).U J) (r.s J) =
      gw w₂ (𝟙 A ≫ ι) y ((J ⟨⟩).1 ⟨⟩) k₂ * (gw w₁ (𝟙 A ≫ ι) y (J ⟨⟩).2 k₂)⁻¹ :=
    hr A (𝟙 A) y ((J ⟨⟩).1 ⟨⟩) (J ⟨⟩).2 k₂ a1 m₁.2 hk₂
  have v₂ : gm (𝟙 A) y (((LB.div (L₂'.pull ψ) L₁).pull jA).U J') (r.s J') =
      gw w₂ (𝟙 A ≫ ι) y ((J' ⟨⟩).1 ⟨⟩) k₂ * (gw w₁ (𝟙 A ≫ ι) y (J' ⟨⟩).2 k₂)⁻¹ :=
    hr A (𝟙 A) y ((J' ⟨⟩).1 ⟨⟩) (J' ⟨⟩).2 k₂ a2 m₂.2 hk₂
  rw [gm_res _ y _ hy, map_mul, gm_res _ y _ hy, gm_div_pull_g jA y J J' hy, v₁, v₂]
  have q₂ := p₂ A (𝟙 A ≫ ι) y ((J ⟨⟩).1 ⟨⟩) ((J' ⟨⟩).1 ⟨⟩) k₂ k₂ (by show F₂ (ι y) ∈ _; rw [pt₂]; exact a1)
    (by show F₂ (ι y) ∈ _; rw [pt₂]; exact a2) hk₂ hk₂
  have q₁ := p₁ A (𝟙 A ≫ ι) y (J ⟨⟩).2 (J' ⟨⟩).2 k₂ k₂ (by show F₁ (ι y) ∈ _; rw [pt₁]; exact m₁.2)
    (by show F₁ (ι y) ∈ _; rw [pt₁]; exact m₂.2) hk₂ hk₂
  rw [gm_self hL₀ (𝟙 A ≫ ι) y hk₂, inv_one, mul_one] at q₁ q₂
  have c₂ : (𝟙 A ≫ ι) ≫ F₂ = jA ≫ ψ := by rw [Category.id_comp, h₂]
  have c₁ : (𝟙 A ≫ ι) ≫ F₁ = jA := by rw [Category.id_comp, h₁]
  rw [q₁, q₂, c₁, c₂, gm_pullG' ψ jA y _ _ ⟨m₁.1, m₂.1⟩]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end GenericGen

section RigPull

open MonoidalCategory CartesianMonoidalCategory

attribute [local instance] Over.cartesianMonoidalCategory

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']

private theorem pullU_pullU_eq_pullU_comp {X Y Z : Scheme.{0}} (b : Z ⟶ Y) (a : Y ⟶ X) (W : X.Opens) (u : Γ(X, W)ˣ) :
    pullU b (a ⁻¹ᵁ W) (pullU a W u) = pullU (b ≫ a) W u := by
  apply Units.ext
  first
    | (simp [pullU]; done)
    | (simp [pullU]; rfl)
    | rfl

private theorem res_pullU_eq_of_eq {P Z : Scheme.{0}} (C C' : P ⟶ Z) (h : C = C') (W : Z.Opens) (u : Γ(Z, W)ˣ)
    {V : P.Opens} (k : V ≤ C ⁻¹ᵁ W) (k' : V ≤ C' ⁻¹ᵁ W) :
    res k (pullU C W u) = res k' (pullU C' W u) := by
  subst h
  rfl

private theorem res_pullU_pullU_eq_of_comp_eq {P Q Q' Z : Scheme.{0}} (A : P ⟶ Q) (B : Q ⟶ Z) (A' : P ⟶ Q') (B' : Q' ⟶ Z)
    (h : A ≫ B = A' ≫ B') (W : Z.Opens) (u : Γ(Z, W)ˣ) {V : P.Opens}
    (k : V ≤ A ⁻¹ᵁ (B ⁻¹ᵁ W)) (k' : V ≤ A' ⁻¹ᵁ (B' ⁻¹ᵁ W)) :
    res k (pullU A _ (pullU B W u)) = res k' (pullU A' _ (pullU B' W u)) := by
  rw [pullU_pullU_eq_pullU_comp, pullU_pullU_eq_pullU_comp]
  exact res_pullU_eq_of_eq _ _ h _ _ _ _

theorem rigPullOf_isGen (F : G'.left ⟶ G.left) (e : (𝟙_ (Over S')).left ⟶ (𝟙_ (Over S)).left)
    (he : eSec G' ≫ F = e ≫ eSec G) (L : LB G.left) (r : LB.Gen (L.pull (eSec G))) (hr : r.IsGen) :
    (rigPullOf F e he L r).IsGen := by
  intro i j
  have hV : ((L.pull F).pull (eSec G')).U i ⊓ ((L.pull F).pull (eSec G')).U j ≤
      e ⁻¹ᵁ ((L.pull (eSec G)).U (fun _ => i ⟨⟩ ⟨⟩) ⊓ (L.pull (eSec G)).U (fun _ => j ⟨⟩ ⟨⟩)) :=
    le_inf (inf_le_left.trans (rigPull_le F e he L i)) (inf_le_right.trans (rigPull_le F e he L j))
  have hr' := congrArg (fun x => res hV (pullU e _ x)) (hr (fun _ => i ⟨⟩ ⟨⟩) (fun _ => j ⟨⟩ ⟨⟩))
  simp only [map_mul, pullU_res_eq_res_preimage_mono, res_res_eq_res_trans'] at hr'
  have hG : res hV (pullU e _ ((L.pull (eSec G)).g (fun _ => i ⟨⟩ ⟨⟩) (fun _ => j ⟨⟩ ⟨⟩))) =
      ((L.pull F).pull (eSec G')).g i j := by
    rw [pull_g_eq_res_pullU_g (P := L) (eSec G) _ _ (pull_U_inf_le_preimage_inf (P := L) (eSec G) _ _), pullU_res_eq_res_preimage_mono, res_res_eq_res_trans',
      pull_g_eq_res_pullU_g (P := L.pull F) (eSec G') i j (pull_U_inf_le_preimage_inf (P := L.pull F) (eSec G') i j),
      pull_g_eq_res_pullU_g (P := L) F (i ⟨⟩) (j ⟨⟩) (pull_U_inf_le_preimage_inf (P := L) F (i ⟨⟩) (j ⟨⟩)), pullU_res_eq_res_preimage_mono, res_res_eq_res_trans']
    exact res_pullU_pullU_eq_of_comp_eq e (eSec G) (eSec G') F he.symm _ _ _ _
  rw [hG] at hr'
  first
    | (erw [← res_res_eq_res_trans' (rigPull_le F e he L i)
          (inf_le_left : ((L.pull F).pull (eSec G')).U i ⊓ ((L.pull F).pull (eSec G')).U j ≤
            ((L.pull F).pull (eSec G')).U i),
        ← res_res_eq_res_trans' (rigPull_le F e he L j)
          (inf_le_right : ((L.pull F).pull (eSec G')).U i ⊓ ((L.pull F).pull (eSec G')).U j ≤
            ((L.pull F).pull (eSec G')).U j)] at hr'
       exact hr')
    | (refine (res_res_eq_res_trans' _ _ _).trans (hr'.trans ?_)
       exact congrArg (fun x => _ * x) (res_res_eq_res_trans' _ _ _).symm)

end RigPull

section Germs

variable {X Y Z : Scheme.{0}}

theorem gm_divPullGen {L M : LB X} (f : Y ⟶ X) (a : LB.Gen (L.pull f)) (b : LB.Gen (M.pull f)) (g : Z ⟶ Y) (z : Z)
    (J : PUnit → M.ι × L.ι) (hz : g z ∈ ((LB.div M L).pull f).U J) :
    gm g z _ ((divPullGen f a b).s J) =
      gm g z _ (b.s (fun _ => (J ⟨⟩).1)) * (gm g z _ (a.s (fun _ => (J ⟨⟩).2)))⁻¹ := by
  show gm g z _ (res (le_div_left f J) (b.s _) * (res (le_div_right f J) (a.s _))⁻¹) = _
  rw [map_mul, map_inv]
  exact congrArg₂ (· * ·) (gm_res g z _ hz _) (congrArg (·⁻¹) (gm_res g z _ hz _))

end Germs

section GermsRig

open MonoidalCategory CartesianMonoidalCategory

attribute [local instance] Over.cartesianMonoidalCategory

variable {S S' Z : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']

theorem gm_rigPullOf (F : G'.left ⟶ G.left) (e : (𝟙_ (Over S')).left ⟶ (𝟙_ (Over S)).left)
    (he : eSec G' ≫ F = e ≫ eSec G) (L : LB G.left) (r : LB.Gen (L.pull (eSec G)))
    (g : Z ⟶ (𝟙_ (Over S')).left) (z : Z) (j : PUnit → PUnit → L.ι) (hz : g z ∈ ((L.pull F).pull (eSec G')).U j) :
    gm g z _ ((rigPullOf F e he L r).s j) = gm (g ≫ e) z _ (r.s (fun _ => j ⟨⟩ ⟨⟩)) := by
  refine (gm_res g z _ hz _).trans (gm_pull g e z _ ?_ _)
  first
    | exact rigPull_le F e he L j hz
    | exact (rigPull_le F e he L j) hz

end GermsRig

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
