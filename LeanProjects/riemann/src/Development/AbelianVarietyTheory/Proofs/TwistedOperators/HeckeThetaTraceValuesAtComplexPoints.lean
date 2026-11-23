import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsCan
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.AbsGeneratorRatioEqOneOfUnitFrameMove
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeIsogenyLiftsToLatticeMapScalingForms
open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
open GlobalTheory.HkFam (admitted)
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.MoveValues

set_option autoImplicit false

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HeckeValues

section Gen

variable {X Y Z : Scheme.{0}} {L : LB X}

theorem g_self (hL : L.IsLB) (f : Y ⟶ X) (y : Y) {i : L.ι} (hi : f y ∈ L.U i) :
    gm f y (L.U i ⊓ L.U i) (L.g i i) = 1 :=
  mul_eq_left.1 (gm_cocycle hL f y hi hi hi)

theorem mem_twoPullbackChart_iff {φ : Fin 2 → (Y ⟶ X)} (r : Z ⟶ Y) (z : Z) (a b : L.ι) :
    r z ∈ LB.wchart L φ ![a, b] ↔ (r ≫ φ 0) z ∈ L.U a ∧ (r ≫ φ 1) z ∈ L.U b := by
  constructor
  · intro h
    exact ⟨Set.mem_iInter.1 h 0, Set.mem_iInter.1 h 1⟩
  · rintro ⟨h0, h1⟩
    refine Set.mem_iInter.2 fun k => ?_
    fin_cases k
    exacts [h0, h1]

theorem gv_trans {φ : Fin 2 → (Y ⟶ X)} {ε : Fin 2 → ℤ} {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen)
    (r : Z ⟶ Y) (z : Z) {a b a' b' : L.ι} (h : r z ∈ LB.wchart L φ ![a, b])
    (h' : r z ∈ LB.wchart L φ ![a', b']) :
    gm r z (LB.wchart L φ ![a, b]) (t.s ![a, b]) =
      gm (r ≫ φ 0) z (L.U a ⊓ L.U a') (L.g a a') ^ ε 0 * gm (r ≫ φ 1) z (L.U b ⊓ L.U b') (L.g b b') ^ ε 1 *
        gm r z (LB.wchart L φ ![a', b']) (t.s ![a', b']) := by
  rw [gen_trans ht r z h h', trF, Fin.prod_univ_two]
  rfl

theorem pullbackGenerator_chart_transition {f : Y ⟶ X} {t : LB.Gen (L.pull f)} (ht : t.IsGen) (r : Z ⟶ Y) (z : Z) {a a' : L.ι}
    (h : (r ≫ f) z ∈ L.U a) (h' : (r ≫ f) z ∈ L.U a') :
    gm r z ((L.pull f).U (fun _ => a)) (t.s (fun _ => a)) =
      gm (r ≫ f) z (L.U a ⊓ L.U a') (L.g a a') * gm r z ((L.pull f).U (fun _ => a')) (t.s (fun _ => a')) := by
  refine (gen_trans ht r z (Set.mem_iInter.2 fun _ => h) (Set.mem_iInter.2 fun _ => h')).trans ?_
  rw [trF, Fintype.prod_unique, zpow_one]
  rfl

theorem pullbackPowerSection_chart_transition {f : Y ⟶ X} (s : LB.Sec (LB.LinComb L (fun _ : Fin 1 => f) (fun _ => 1))) (r : Z ⟶ Y) (z : Z)
    {a a' : L.ι} (h : (r ≫ f) z ∈ L.U a) (h' : (r ≫ f) z ∈ L.U a') :
    gs r z (LB.wchart L (fun _ : Fin 1 => f) (fun _ => a)) (s.f (fun _ => a)) =
      (gm (r ≫ f) z (L.U a ⊓ L.U a') (L.g a a')).val *
        gs r z (LB.wchart L (fun _ : Fin 1 => f) (fun _ => a')) (s.f (fun _ => a')) := by
  rw [sec_trans s r z (Set.mem_iInter.2 fun _ => h) (Set.mem_iInter.2 fun _ => h'), trF, Fin.prod_univ_one,
    zpow_one]

end Gen

section Pts

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {x : Sp ℂ ⟶ S}

abbrev rpt (a : Over.mk x ⟶ A) : Sp ℂ ⟶ (Over.mk x ⊗ A).left := (lift (𝟙 (Over.mk x)) a).left

abbrev pl (a : Over.mk x ⟶ A) : Sp ℂ ⟶ A.left := a.left

theorem rpt_snd (a : Over.mk x ⟶ A) : rpt a ≫ (snd (Over.mk x) A).left = pl a := lift_l_snd _ _

theorem rpt_mulT (a : Over.mk x ⟶ A) (p : ℕ) : rpt a ≫ (mulT A (Over.mk x) p).left = rpt (a ^ p) := by
  rw [← Over.comp_left, mulT, comp_lift, lift_fst, MonObj.comp_pow, lift_snd]

theorem rpt_transl (a c : Over.mk x ⟶ A) : rpt a ≫ (translT A c).left = rpt (c * a) := by
  rw [← Over.comp_left, lift_transl, Category.id_comp]

end Pts

section Core

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] (L : RigLB A) {x x' : Sp ℂ ⟶ S}
  {Ψ : (Over.mk x ⊗ A).left ⟶ (Over.mk x' ⊗ A).left} {p : ℕ}
  (β : LB.Gen (isoLB A L Ψ ((p : ℤ) ^ 2))) (β₀ : LB.Gen (isoLB A L (mulT A (Over.mk x) p).left ((p : ℤ) ^ 2)))

def kc (a : Over.mk x ⟶ A) : L.L.ι := (exists_chart L.isLB (a.left cpt)).choose

theorem kc_mem (a : Over.mk x ⟶ A) : pl a cpt ∈ L.L.U (kc L a) := (exists_chart L.isLB (a.left cpt)).choose_spec

def W (r : Sp ℂ ⟶ (Over.mk x ⊗ A).left) (k j i : L.L.ι) : ((Sp ℂ).presheaf.stalk cpt)ˣ :=
  gm r cpt (LB.wchart L.L (isoφ A (mulT A (Over.mk x) p).left) ![k, j]) (β₀.s ![k, j]) *
    (gm r cpt (LB.wchart L.L (isoφ A Ψ) ![k, i]) (β.s ![k, i]))⁻¹

variable {L β β₀}

theorem fiberComplexPoint_mem_thetaTraceChart_of_mem (a : Over.mk x ⟶ A) {k j : L.L.ι} (hk : pl a cpt ∈ L.L.U k) (hj : pl (a ^ p) cpt ∈ L.L.U j) :
    rpt a cpt ∈ LB.wchart L.L (isoφ A (mulT A (Over.mk x) p).left) ![k, j] := by
  refine (mem_twoPullbackChart_iff _ _ _ _).2 ⟨?_, ?_⟩
  · show (rpt a ≫ (snd (Over.mk x) A).left) cpt ∈ _
    rw [rpt_snd]; exact hk
  · show (rpt a ≫ (mulT A (Over.mk x) p).left ≫ (snd (Over.mk x) A).left) cpt ∈ _
    rw [← Category.assoc, rpt_mulT, rpt_snd]; exact hj

theorem fiberComplexPoint_mem_thetaTraceIsoChart_of_comp (a : Over.mk x ⟶ A) (ψa : Over.mk x' ⟶ A) (ha : rpt a ≫ Ψ = rpt ψa) {k i : L.L.ι}
    (hk : pl a cpt ∈ L.L.U k) (hi : pl ψa cpt ∈ L.L.U i) :
    rpt a cpt ∈ LB.wchart L.L (isoφ A Ψ) ![k, i] := by
  refine (mem_twoPullbackChart_iff _ _ _ _).2 ⟨?_, ?_⟩
  · show (rpt a ≫ (snd (Over.mk x) A).left) cpt ∈ _
    rw [rpt_snd]; exact hk
  · show (rpt a ≫ Ψ ≫ (snd (Over.mk x') A).left) cpt ∈ _
    rw [← Category.assoc, ha, rpt_snd]; exact hi

theorem W_trans (hβ : β.IsGen) (hβ₀ : β₀.IsGen) (a : Over.mk x ⟶ A) (ψa : Over.mk x' ⟶ A) (ha : rpt a ≫ Ψ = rpt ψa)
    {k j i k' j' i' : L.L.ι} (hk : pl a cpt ∈ L.L.U k) (hk' : pl a cpt ∈ L.L.U k')
    (hj : pl (a ^ p) cpt ∈ L.L.U j) (hj' : pl (a ^ p) cpt ∈ L.L.U j')
    (hi : pl ψa cpt ∈ L.L.U i) (hi' : pl ψa cpt ∈ L.L.U i') :
    W L β β₀ (rpt a) k j i * gm (pl (a ^ p)) cpt (L.L.U j ⊓ L.L.U j') (L.L.g j j') =
      gm (pl ψa) cpt (L.L.U i ⊓ L.L.U i') (L.L.g i i') * W L β β₀ (rpt a) k' j' i' := by
  have e0 : rpt a ≫ isoφ A (mulT A (Over.mk x) p).left 0 = pl a := rpt_snd a
  have e0' : rpt a ≫ isoφ A Ψ 0 = pl a := rpt_snd a
  have e1 : rpt a ≫ isoφ A (mulT A (Over.mk x) p).left 1 = pl (a ^ p) := by
    show rpt a ≫ (mulT A (Over.mk x) p).left ≫ (snd (Over.mk x) A).left = _
    rw [← Category.assoc, rpt_mulT, rpt_snd]
  have f1 : rpt a ≫ isoφ A Ψ 1 = pl ψa := by
    show rpt a ≫ Ψ ≫ (snd (Over.mk x') A).left = _
    rw [← Category.assoc, ha, rpt_snd]
  unfold W
  rw [gv_trans hβ₀ (rpt a) cpt (fiberComplexPoint_mem_thetaTraceChart_of_mem a hk hj) (fiberComplexPoint_mem_thetaTraceChart_of_mem a hk' hj'),
    gv_trans hβ (rpt a) cpt (fiberComplexPoint_mem_thetaTraceIsoChart_of_comp a ψa ha hk hi) (fiberComplexPoint_mem_thetaTraceIsoChart_of_comp a ψa ha hk' hi'), e0, e0', e1, f1]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero]
  abel

end Core

section Vals

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] (L : RigLB A) {x x' : Sp ℂ ⟶ S}
  {Ψ : (Over.mk x ⊗ A).left ⟶ (Over.mk x' ⊗ A).left} {p : ℕ}
  (β : LB.Gen (isoLB A L Ψ ((p : ℤ) ^ 2))) (β₀ : LB.Gen (isoLB A L (mulT A (Over.mk x) p).left ((p : ℤ) ^ 2)))

def bv (i j : L.L.ι) (a : Over.mk x ⟶ A) : ℂ := ev (W L β β₀ (rpt a) (kc L a) j i).val

variable {L β β₀}

theorem bv_ne (i j : L.L.ι) (a : Over.mk x ⟶ A) : bv L β β₀ i j a ≠ 0 :=
  ((W L β β₀ (rpt a) (kc L a) j i).isUnit.map ev).ne_zero

theorem W_eq (hβ : β.IsGen) (hβ₀ : β₀.IsGen) (a : Over.mk x ⟶ A) (ψa : Over.mk x' ⟶ A) (ha : rpt a ≫ Ψ = rpt ψa)
    {k j i : L.L.ι} (hk : pl a cpt ∈ L.L.U k) (hj : pl (a ^ p) cpt ∈ L.L.U j) (hi : pl ψa cpt ∈ L.L.U i) :
    W L β β₀ (rpt a) k j i = W L β β₀ (rpt a) (kc L a) j i := by
  have e := W_trans hβ hβ₀ a ψa ha hk (kc_mem L a) hj hj hi hi
  rwa [g_self L.isLB _ _ hj, g_self L.isLB _ _ hi, _root_.mul_one, _root_.one_mul] at e

theorem bv_trans (hβ : β.IsGen) (hβ₀ : β₀.IsGen) (a : Over.mk x ⟶ A) (ψa : Over.mk x' ⟶ A) (ha : rpt a ≫ Ψ = rpt ψa)
    {i j i' j' : L.L.ι} (hi : pl ψa cpt ∈ L.L.U i) (hi' : pl ψa cpt ∈ L.L.U i')
    (hj : pl (a ^ p) cpt ∈ L.L.U j) (hj' : pl (a ^ p) cpt ∈ L.L.U j') :
    bv L β β₀ i j a * valAt' (pl (a ^ p)) (L.L.U j ⊓ L.L.U j') (L.L.g j j').val =
      valAt' (pl ψa) (L.L.U i ⊓ L.L.U i') (L.L.g i i').val * bv L β β₀ i' j' a := by
  have e := congrArg (fun u : ((Sp ℂ).presheaf.stalk cpt)ˣ => ev u.val)
    (W_trans hβ hβ₀ a ψa ha (kc_mem L a) (kc_mem L a) hj hj' hi hi')
  simp only [Units.val_mul, map_mul] at e
  rw [ev_gm (pl (a ^ p)) (L.L.U j ⊓ L.L.U j') ⟨hj, hj'⟩, ev_gm (pl ψa) (L.L.U i ⊓ L.L.U i') ⟨hi, hi'⟩] at e
  exact e

end Vals

section Sum

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x x' : Sp ℂ ⟶ S}
  {Ψ : (Over.mk x ⊗ A).left ⟶ (Over.mk x' ⊗ A).left} {p : ℕ}
  {β : LB.Gen (isoLB A L Ψ ((p : ℤ) ^ 2))} {β₀ : LB.Gen (isoLB A L (mulT A (Over.mk x) p).left ((p : ℤ) ^ 2))}

theorem bv_values (hβ : β.IsGen) (hβ₀ : β₀.IsGen) {s : LB.Sec (LPow A L.L 1 (Over.mk x))}
    {s₁ : LB.Sec (LPow A L.L ((p : ℤ) ^ 2) (Over.mk x))} {s' : LB.Sec (LPow A L.L 1 (Over.mk x'))}
    (hc₀ : IsCarried A L (mulT A (Over.mk x) p).left _ β₀ s s₁) {n : ℕ} (cr : Fin n → (Over.mk x ⟶ A))
    (hcr : ∀ m, cr m ∈ transKer A Ψ)
    (hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ (Over.mk x ⊗ A).left) (z : Z) (J), Good L.L z J →
      sv A L s' (r ≫ Ψ) z J = ∑ i, ((val β (r ≫ (translT A (cr i)).left) z J)⁻¹).val *
        sv A L s₁ (r ≫ (translT A (cr i)).left) z J)
    (a : Over.mk x ⟶ A) (ψa : Over.mk x' ⟶ A) (ha : rpt a ≫ Ψ = rpt ψa) (i : L.L.ι) (jm : Fin n → L.L.ι)
    (hi : pl ψa cpt ∈ L.L.U i) (hj : ∀ m, pl ((cr m * a) ^ p) cpt ∈ L.L.U (jm m)) :
    valAt' (rpt ψa) ((LPow A L.L 1 (Over.mk x')).U (fun _ => i)) (s'.f (fun _ => i)) =
      ∑ m, bv L β β₀ i (jm m) (cr m * a) *
        valAt' (rpt ((cr m * a) ^ p)) ((LPow A L.L 1 (Over.mk x)).U (fun _ => jm m)) (s.f (fun _ => jm m)) := by
  obtain ⟨J, hJ, hJi⟩ := exists_good L.L L.isLB cpt (fun _ : Unit => pl ψa) (fun _ => i) (fun _ _ _ => rfl)
    (fun _ => hi)
  have H := hv _ (rpt a) cpt J hJ
  rw [ha] at H
  have hl : sv A L s' (rpt ψa) cpt J =
      gs (rpt ψa) cpt ((LPow A L.L 1 (Over.mk x')).U (fun _ => i)) (s'.f (fun _ => i)) :=
    sval_of _ _ _ _ _ fun _ => (congrArg J (rpt_snd ψa)).trans (hJi ())
  have ml : rpt ψa cpt ∈ (LPow A L.L 1 (Over.mk x')).U (fun _ => i) :=
    Set.mem_iInter.2 fun _ => by
      show (rpt ψa ≫ (snd (Over.mk x') A).left) cpt ∈ L.L.U i
      rw [rpt_snd]; exact hi
  rw [← ev_gs (rpt ψa) _ ml (s'.f fun _ => i), ← hl, H, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [rpt_transl]
  set c := cr m * a with hc
  have hcΨ : rpt c ≫ Ψ = rpt ψa := by
    rw [hc, ← rpt_transl, Category.assoc, mem_transKer.1 (hcr m), ha]
  have hmul : rpt c ≫ (mulT A (Over.mk x) p).left = rpt (c ^ p) := rpt_mulT c p
  rw [hc₀.val _ cpt hJ, hmul]
  have v0 : val β₀ (rpt c) cpt J = gm (rpt c) cpt
      (LB.wchart L.L (isoφ A (mulT A (Over.mk x) p).left) ![J (pl c), J (pl (c ^ p))])
      (β₀.s ![J (pl c), J (pl (c ^ p))]) :=
    val_of _ _ _ _ _ fun k => by
      fin_cases k
      · exact congrArg J (rpt_snd c)
      · show J (rpt c ≫ (mulT A (Over.mk x) p).left ≫ (snd (Over.mk x) A).left) = _
        rw [← Category.assoc, hmul, rpt_snd]; rfl
  have v1 : val β (rpt c) cpt J =
      gm (rpt c) cpt (LB.wchart L.L (isoφ A Ψ) ![J (pl c), i]) (β.s ![J (pl c), i]) :=
    val_of _ _ _ _ _ fun k => by
      fin_cases k
      · exact congrArg J (rpt_snd c)
      · show J (rpt c ≫ Ψ ≫ (snd (Over.mk x') A).left) = _
        rw [← Category.assoc, hcΨ, rpt_snd]; exact hJi ()
  have s0 : sv A L s (rpt (c ^ p)) cpt J = gs (rpt (c ^ p)) cpt
      ((LPow A L.L 1 (Over.mk x)).U (fun _ => J (pl (c ^ p)))) (s.f (fun _ => J (pl (c ^ p)))) :=
    sval_of _ _ _ _ _ fun _ => congrArg J (rpt_snd _)
  have hk : pl c cpt ∈ L.L.U (J (pl c)) := hJ _
  have hj' : pl (c ^ p) cpt ∈ L.L.U (J (pl (c ^ p))) := hJ _
  have et := W_trans hβ hβ₀ c ψa hcΨ hk (kc_mem L c) hj' (hj m) hi hi
  rw [g_self L.isLB _ _ hi, _root_.one_mul] at et
  have st : gs (rpt (c ^ p)) cpt ((LPow A L.L 1 (Over.mk x)).U (fun _ => J (pl (c ^ p))))
      (s.f (fun _ => J (pl (c ^ p)))) =
      (gm (pl (c ^ p)) cpt (L.L.U (J (pl (c ^ p))) ⊓ L.L.U (jm m)) (L.L.g (J (pl (c ^ p))) (jm m))).val *
        gs (rpt (c ^ p)) cpt ((LPow A L.L 1 (Over.mk x)).U (fun _ => jm m)) (s.f (fun _ => jm m)) := by
    have e := pullbackPowerSection_chart_transition (f := (snd (Over.mk x) A).left) s (rpt (c ^ p)) cpt (a := J (pl (c ^ p))) (a' := jm m)
      (by rw [rpt_snd]; exact hj') (by rw [rpt_snd]; exact hj m)
    rw [rpt_snd] at e
    exact e
  have mj : rpt (c ^ p) cpt ∈ (LPow A L.L 1 (Over.mk x)).U (fun _ => jm m) :=
    Set.mem_iInter.2 fun _ => by
      show (rpt (c ^ p) ≫ (snd (Over.mk x) A).left) cpt ∈ L.L.U (jm m)
      rw [rpt_snd]; exact hj m
  rw [s0, v0, v1, bv, ← ev_gs _ _ mj (s.f fun _ => jm m), ← map_mul, ← et]
  unfold W
  simp only [Units.val_mul]
  rw [st]
  ring_nf

end Sum

section Hol

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x x' : Sp ℂ ⟶ S}
  {Ψ : (Over.mk x ⊗ A).left ⟶ (Over.mk x' ⊗ A).left} {p : ℕ}
  {β : LB.Gen (isoLB A L Ψ ((p : ℤ) ^ 2))} {β₀ : LB.Gen (isoLB A L (mulT A (Over.mk x) p).left ((p : ℤ) ^ 2))}

theorem ev_inv (u : ((Sp ℂ).presheaf.stalk cpt)ˣ) : ev (u⁻¹).val = (ev u.val)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])

theorem bv_hol (hβ : β.IsGen) (hβ₀ : β₀.IsGen) (ψp : (Over.mk x ⟶ A) → (Over.mk x' ⟶ A))
    (hΨ : ∀ a, rpt a ≫ Ψ = rpt (ψp a)) {g : ℕ} (e : (Fin g → ℂ) → (Over.mk x ⟶ A))
    (he : IsHolTo Set.univ (fun w => rpt (e w))) (i j : L.L.ι) :
    DifferentiableOn ℂ (fun w => bv L β β₀ i j (e w))
      {w | ⊤ ≤ pl (ψp (e w)) ⁻¹ᵁ L.L.U i ∧ ⊤ ≤ pl (e w ^ p) ⁻¹ᵁ L.L.U j} := by
  intro w₀ hw₀
  obtain ⟨o₀, d₀⟩ := he (LB.wchart L.L (isoφ A (mulT A (Over.mk x) p).left) ![kc L (e w₀), j])
    (β₀.s ![kc L (e w₀), j]).val
  obtain ⟨o₁, d₁⟩ := he (LB.wchart L.L (isoφ A Ψ) ![kc L (e w₀), i]) (β.s ![kc L (e w₀), i]).val
  have hN := o₀.inter o₁
  have key : ∀ w ∈ {b ∈ (Set.univ : Set (Fin g → ℂ)) | ⊤ ≤ rpt (e b) ⁻¹ᵁ
        LB.wchart L.L (isoφ A (mulT A (Over.mk x) p).left) ![kc L (e w₀), j]} ∩
      {b ∈ (Set.univ : Set (Fin g → ℂ)) | ⊤ ≤ rpt (e b) ⁻¹ᵁ LB.wchart L.L (isoφ A Ψ) ![kc L (e w₀), i]},
      bv L β β₀ i j (e w) =
        valAt' (rpt (e w)) (LB.wchart L.L (isoφ A (mulT A (Over.mk x) p).left) ![kc L (e w₀), j])
            (β₀.s ![kc L (e w₀), j]).val *
          (valAt' (rpt (e w)) (LB.wchart L.L (isoφ A Ψ) ![kc L (e w₀), i]) (β.s ![kc L (e w₀), i]).val)⁻¹ := by
    rintro w ⟨⟨-, h0⟩, ⟨-, h1⟩⟩
    have m0 : rpt (e w) cpt ∈ LB.wchart L.L (isoφ A (mulT A (Over.mk x) p).left) ![kc L (e w₀), j] :=
      (mem_iff _ _).2 h0
    have m1 : rpt (e w) cpt ∈ LB.wchart L.L (isoφ A Ψ) ![kc L (e w₀), i] := (mem_iff _ _).2 h1
    obtain ⟨a0, a1⟩ := (mem_twoPullbackChart_iff _ _ _ _).1 m0
    obtain ⟨-, b1⟩ := (mem_twoPullbackChart_iff _ _ _ _).1 m1
    have hk : pl (e w) cpt ∈ L.L.U (kc L (e w₀)) := by
      rwa [show rpt (e w) ≫ isoφ A (mulT A (Over.mk x) p).left 0 = pl (e w) from rpt_snd _] at a0
    have hj : pl (e w ^ p) cpt ∈ L.L.U j := by
      rwa [show rpt (e w) ≫ isoφ A (mulT A (Over.mk x) p).left 1 = pl (e w ^ p) by
        show rpt (e w) ≫ (mulT A (Over.mk x) p).left ≫ (snd (Over.mk x) A).left = _
        rw [← Category.assoc, rpt_mulT, rpt_snd]] at a1
    have hi : pl (ψp (e w)) cpt ∈ L.L.U i := by
      rwa [show rpt (e w) ≫ isoφ A Ψ 1 = pl (ψp (e w)) by
        show rpt (e w) ≫ Ψ ≫ (snd (Over.mk x') A).left = _
        rw [← Category.assoc, hΨ, rpt_snd]] at b1
    rw [bv, ← W_eq hβ hβ₀ (e w) (ψp (e w)) (hΨ _) hk hj hi, W, Units.val_mul, map_mul,
      ev_gm _ _ m0 (β₀.s ![kc L (e w₀), j]), ev_inv, ev_gm _ _ m1 (β.s ![kc L (e w₀), i])]
  have hf := (d₀.mono Set.inter_subset_left).mul ((d₁.mono Set.inter_subset_right).inv fun w hw => by
    have m1 : rpt (e w) cpt ∈ LB.wchart L.L (isoφ A Ψ) ![kc L (e w₀), i] := (mem_iff _ _).2 hw.2.2
    show valAt' (rpt (e w)) _ _ ≠ 0
    rw [← ev_gm _ _ m1 (β.s ![kc L (e w₀), i])]
    exact ((Units.isUnit _).map ev).ne_zero)
  have hw : w₀ ∈ {b ∈ (Set.univ : Set (Fin g → ℂ)) | ⊤ ≤ rpt (e b) ⁻¹ᵁ
        LB.wchart L.L (isoφ A (mulT A (Over.mk x) p).left) ![kc L (e w₀), j]} ∩
      {b ∈ (Set.univ : Set (Fin g → ℂ)) | ⊤ ≤ rpt (e b) ⁻¹ᵁ LB.wchart L.L (isoφ A Ψ) ![kc L (e w₀), i]} :=
    ⟨⟨trivial, (mem_iff _ _).1 (fiberComplexPoint_mem_thetaTraceChart_of_mem (e w₀) (kc_mem L _) ((mem_iff _ _).2 hw₀.2))⟩,
      ⟨trivial, (mem_iff _ _).1 (fiberComplexPoint_mem_thetaTraceIsoChart_of_comp (e w₀) (ψp (e w₀)) (hΨ _) (kc_mem L _) ((mem_iff _ _).2 hw₀.1))⟩⟩
  exact ((hf.differentiableAt (hN.mem_nhds hw)).congr_of_eventuallyEq
    (Filter.eventually_of_mem (hN.mem_nhds hw) key)).differentiableWithinAt

end Hol

section Rig

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x x' : Sp ℂ ⟶ S}
  {Ψ : (Over.mk x ⊗ A).left ⟶ (Over.mk x' ⊗ A).left} {p : ℕ}
  {β : LB.Gen (isoLB A L Ψ ((p : ℤ) ^ 2))} {β₀ : LB.Gen (isoLB A L (mulT A (Over.mk x) p).left ((p : ℤ) ^ 2))}

theorem val_origin {y y' : Sp ℂ ⟶ S} {Φ : (Over.mk y ⊗ A).left ⟶ (Over.mk y' ⊗ A).left} {k : ℤ}
    {t : LB.Gen (isoLB A L Φ k)} (h : IsRigIso A L Φ k t) {J : (Sp ℂ ⟶ A.left) → L.L.ι} (hJ : Good L.L cpt J) :
    val t (rpt (1 : Over.mk y ⟶ A)) cpt J =
      val (L := L.L) (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) L.rig (𝟙 (Sp ℂ) ≫ y) cpt J ^ k *
        val (L := L.L) (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) L.rig (𝟙 (Sp ℂ) ≫ y') cpt J ^ (-1 : ℤ) := by
  have e : rpt (1 : Over.mk y ⟶ A) = 𝟙 (Sp ℂ) ≫ (ptSecT A (1 : Over.mk y ⟶ A)).left := (Category.id_comp _).symm
  rw [e]
  exact (val_pull hJ _ _ _).symm.trans ((val_corr hJ h.2.2 (𝟙 _)).trans ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) (val_rigT (Over.mk y) _ (𝟙 _) cpt hJ) (val_rigT (Over.mk y') _ (𝟙 _) cpt hJ))))

theorem rig_ev (y : Sp ℂ ⟶ S) (i : L.L.ι) (h : (y ≫ eSec A) cpt ∈ L.L.U i) :
    ev (gm y cpt ((L.L.pull (eSec A)).U (fun _ => i)) (L.rig.s (fun _ => i))).val =
      valAt' y ((L.L.pull (eSec A)).U (fun _ => i)) (L.rig.s (fun _ => i)).val := by
  have m : y cpt ∈ LB.wchart L.L (fun _ : PUnit => eSec A) (fun _ => i) := Set.mem_iInter.2 fun _ => h
  exact ev_gm y _ m _

theorem rig_trans (y : Sp ℂ ⟶ S) {i i' : L.L.ι} (h : (y ≫ eSec A) cpt ∈ L.L.U i) (h' : (y ≫ eSec A) cpt ∈ L.L.U i') :
    valAt' y ((L.L.pull (eSec A)).U (fun _ => i)) (L.rig.s (fun _ => i)).val =
      valAt' (y ≫ eSec A) (L.L.U i ⊓ L.L.U i') (L.L.g i i').val *
        valAt' y ((L.L.pull (eSec A)).U (fun _ => i')) (L.rig.s (fun _ => i')).val := by
  rw [← rig_ev y i h, ← rig_ev y i' h', ← ev_gm (y ≫ eSec A) (L.L.U i ⊓ L.L.U i') ⟨h, h'⟩, ← map_mul,
    ← Units.val_mul, pullbackGenerator_chart_transition L.rigGen y cpt h h']

theorem bv_rig (hβ : IsRigIso A L Ψ _ β) (hβ₀ : IsRigIso A L (mulT A (Over.mk x) p).left _ β₀)
    (h1 : rpt (1 : Over.mk x ⟶ A) ≫ Ψ = rpt (1 : Over.mk x' ⟶ A)) (i j : L.L.ι)
    (hi : pl (1 : Over.mk x' ⟶ A) cpt ∈ L.L.U i) (hj : pl (1 : Over.mk x ⟶ A) cpt ∈ L.L.U j) :
    valAt' x' ((L.L.pull (eSec A)).U (fun _ => i)) (L.rig.s (fun _ => i)).val =
      bv L β β₀ i j 1 * valAt' x ((L.L.pull (eSec A)).U (fun _ => j)) (L.rig.s (fun _ => j)).val := by
  choose J hJ using fun χ : Sp ℂ ⟶ A.left => exists_chart L.isLB (χ cpt)
  have hG : Good L.L cpt J := hJ
  have hp1 : (1 : Over.mk x ⟶ A) ^ p = 1 := one_pow p
  have r0 := val_origin hβ₀ hG
  have r1 := val_origin hβ hG
  have v0 : val β₀ (rpt (1 : Over.mk x ⟶ A)) cpt J =
      gm (rpt (1 : Over.mk x ⟶ A)) cpt (LB.wchart L.L (isoφ A (mulT A (Over.mk x) p).left)
        ![J (pl (1 : Over.mk x ⟶ A)), J (pl (1 : Over.mk x ⟶ A))])
        (β₀.s ![J (pl (1 : Over.mk x ⟶ A)), J (pl (1 : Over.mk x ⟶ A))]) :=
    val_of _ _ _ _ _ fun k => by
      fin_cases k
      · exact congrArg J (rpt_snd _)
      · show J (rpt _ ≫ (mulT A (Over.mk x) p).left ≫ (snd (Over.mk x) A).left) = _
        rw [← Category.assoc, rpt_mulT, rpt_snd, hp1]; rfl
  have v1 : val β (rpt (1 : Over.mk x ⟶ A)) cpt J =
      gm (rpt (1 : Over.mk x ⟶ A)) cpt (LB.wchart L.L (isoφ A Ψ)
        ![J (pl (1 : Over.mk x ⟶ A)), J (pl (1 : Over.mk x' ⟶ A))])
        (β.s ![J (pl (1 : Over.mk x ⟶ A)), J (pl (1 : Over.mk x' ⟶ A))]) :=
    val_of _ _ _ _ _ fun k => by
      fin_cases k
      · exact congrArg J (rpt_snd _)
      · show J (rpt _ ≫ Ψ ≫ (snd (Over.mk x') A).left) = _
        rw [← Category.assoc, h1, rpt_snd]; rfl
  have q0 : val (L := L.L) (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) L.rig (𝟙 (Sp ℂ) ≫ x) cpt J =
      gm x cpt ((L.L.pull (eSec A)).U (fun _ => J (pl (1 : Over.mk x ⟶ A))))
        (L.rig.s (fun _ => J (pl (1 : Over.mk x ⟶ A)))) := by
    rw [val_of _ _ _ _ (fun _ => J (pl (1 : Over.mk x ⟶ A))) fun _ => by rw [Category.id_comp]; rfl,
      Category.id_comp]
    rfl
  have q1 : val (L := L.L) (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) L.rig (𝟙 (Sp ℂ) ≫ x') cpt J =
      gm x' cpt ((L.L.pull (eSec A)).U (fun _ => J (pl (1 : Over.mk x' ⟶ A))))
        (L.rig.s (fun _ => J (pl (1 : Over.mk x' ⟶ A)))) := by
    rw [val_of _ _ _ _ (fun _ => J (pl (1 : Over.mk x' ⟶ A))) fun _ => by rw [Category.id_comp]; rfl,
      Category.id_comp]
    rfl
  have key : W L β β₀ (rpt (1 : Over.mk x ⟶ A)) (J (pl (1 : Over.mk x ⟶ A))) (J (pl (1 : Over.mk x ⟶ A)))
      (J (pl (1 : Over.mk x' ⟶ A))) * gm x cpt ((L.L.pull (eSec A)).U (fun _ => J (pl (1 : Over.mk x ⟶ A))))
        (L.rig.s (fun _ => J (pl (1 : Over.mk x ⟶ A)))) =
      gm x' cpt ((L.L.pull (eSec A)).U (fun _ => J (pl (1 : Over.mk x' ⟶ A))))
        (L.rig.s (fun _ => J (pl (1 : Over.mk x' ⟶ A)))) := by
    rw [W, ← v0, ← v1, r0, r1, q0, q1]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
    abel
  have hj1 : pl ((1 : Over.mk x ⟶ A) ^ p) cpt ∈ L.L.U (J (pl (1 : Over.mk x ⟶ A))) := by rw [hp1]; exact hJ _
  rw [W_eq hβ.2.1 hβ₀.2.1 1 1 h1 (hJ _) hj1 (hJ _)] at key
  have e4 := congrArg (fun u : ((Sp ℂ).presheaf.stalk cpt)ˣ => ev u.val) key
  simp only [Units.val_mul, map_mul] at e4
  rw [rig_ev x _ (hJ (pl (1 : Over.mk x ⟶ A))), rig_ev x' _ (hJ (pl (1 : Over.mk x' ⟶ A)))] at e4
  replace e4 : bv L β β₀ (J (pl (1 : Over.mk x' ⟶ A))) (J (pl (1 : Over.mk x ⟶ A))) 1 * _ = _ := e4
  have e1 := rig_trans x' (i := i) (i' := J (pl (1 : Over.mk x' ⟶ A))) hi (hJ (pl (1 : Over.mk x' ⟶ A)))
  have e2 := rig_trans x (i := j) (i' := J (pl (1 : Over.mk x ⟶ A))) hj (hJ (pl (1 : Over.mk x ⟶ A)))
  have e3 := bv_trans (β := β) (β₀ := β₀) hβ.2.1 hβ₀.2.1 1 1 h1 hi (hJ (pl (1 : Over.mk x' ⟶ A))) (by rw [hp1]; exact hj) hj1
  rw [hp1] at e3
  change bv L β β₀ i j 1 * valAt' (x ≫ eSec A) _ _ = valAt' (x' ≫ eSec A) _ _ * _ at e3
  rw [e1, e2]
  linear_combination (-(valAt' x ((L.L.pull (eSec A)).U (fun _ => J (pl (1 : Over.mk x ⟶ A))))
    (L.rig.s (fun _ => J (pl (1 : Over.mk x ⟶ A)))).val)) * e3 -
    valAt' (x' ≫ eSec A) (L.L.U i ⊓ L.L.U (J (pl (1 : Over.mk x' ⟶ A))))
      (L.L.g i (J (pl (1 : Over.mk x' ⟶ A)))).val * e4

end Rig

theorem hkPtC_values : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (p : ℕ) (y z : FrPt Xo c (CAt σ)) (C : Subgroup (Over.mk y.x ⟶ Xo.univ.t.G)),
  HkPtC p y C z →
  ∃ (ψ : pullback Xo.univ.t.G.hom y.x ⟶ pullback Xo.univ.t.G.hom z.x)
    (ψp : (Over.mk y.x ⟶ Xo.univ.t.G) →* (Over.mk z.x ⟶ Xo.univ.t.G)) (n : ℕ)
    (cr : Fin n → (Over.mk y.x ⟶ Xo.univ.t.G)) (b : Xo.univ.t.PP.L.ι → Xo.univ.t.PP.L.ι → (Over.mk y.x ⟶ Xo.univ.t.G) → ℂ),
    @IsHkIsog E _ _ _ H Dw l Xo (CAt σ) (fieldCAt σ) (algClosedCAt σ) p y.x z.x C ψ ψp ∧ GlobalTheory.ThetaTrace.IsRepsModTors C p cr ∧
    (∀ i j (a : Over.mk y.x ⟶ Xo.univ.t.G), ⊤ ≤ (ψp a).left ⁻¹ᵁ Xo.univ.t.PP.L.U i → ⊤ ≤ (a ^ p).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → b i j a ≠ 0) ∧
    (∀ i j i' j' (a : Over.mk y.x ⟶ Xo.univ.t.G), ⊤ ≤ (ψp a).left ⁻¹ᵁ (Xo.univ.t.PP.L.U i ⊓ Xo.univ.t.PP.L.U i') →
      ⊤ ≤ (a ^ p).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
      b i j a * valAt' (a ^ p).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j').val =
        valAt' (ψp a).left (Xo.univ.t.PP.L.U i ⊓ Xo.univ.t.PP.L.U i') (Xo.univ.t.PP.L.g i i').val * b i' j' a) ∧
    (∀ i j, ⊤ ≤ (1 : Over.mk z.x ⟶ Xo.univ.t.G).left ⁻¹ᵁ Xo.univ.t.PP.L.U i →
      ⊤ ≤ (1 : Over.mk y.x ⟶ Xo.univ.t.G).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' z.x ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => i)) (Xo.univ.t.PP.rig.s (fun _ => i)).val =
        b i j 1 * valAt' y.x ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j)) (Xo.univ.t.PP.rig.s (fun _ => j)).val) ∧
    (∀ (g : ℕ) (e : (Fin g → ℂ) → (Over.mk y.x ⟶ Xo.univ.t.G)), IsHolTo Set.univ (fun w => (e w).left) →
      ∀ i j, DifferentiableOn ℂ (fun w => b i j (e w))
        {w | ⊤ ≤ (ψp (e w)).left ⁻¹ᵁ Xo.univ.t.PP.L.U i ∧ ⊤ ≤ (e w ^ p).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) ∧
    (∀ (a : Over.mk y.x ⟶ Xo.univ.t.G) i (jm : Fin n → Xo.univ.t.PP.L.ι), ⊤ ≤ (ψp a).left ⁻¹ᵁ Xo.univ.t.PP.L.U i →
      (∀ m, ⊤ ≤ ((cr m * a) ^ p).left ⁻¹ᵁ Xo.univ.t.PP.L.U (jm m)) →
      valAt' (lift (𝟙 (Over.mk z.x)) (ψp a)).left ((PPx z.x).U (fun _ => i)) (z.s.f (fun _ => i)) =
        ∑ m, b i (jm m) (cr m * a) *
          valAt' (lift (𝟙 (Over.mk y.x)) ((cr m * a) ^ p)).left ((PPx y.x).U (fun _ => jm m)) (y.s.f (fun _ => jm m))) := by
  intro E _ _ _ H Dw l Xo c σ p y z C hk
  letI := fieldCAt σ
  haveI := algClosedCAt σ
  obtain ⟨ψ, ψp, hiso, -, htr⟩ := hk
  obtain ⟨β, s₁, n, cr, hβ, hs, hr, hv⟩ := isThetaTrace_iff.1 htr
  obtain ⟨β₀, hβ₀, hc₀⟩ := hs.exists_isRigIso
  have hK := transKer_of_isHkIsog hiso
  have hΨ : ∀ a, rpt a ≫ conj y.x z.x ψ = rpt (ψp a) := fun a => (sends_conj_iff ψ _ _).2 (hiso.2.2.1 a)
  refine ⟨ψ, ψp, n, cr, fun i j a => bv Xo.univ.t.PP β β₀ i j a, hiso, hK ▸ hr, fun i j a _ _ => bv_ne i j a,
    fun i j i' j' a hi hj => ?_, fun i j hi hj => ?_, fun g e he i j => ?_, fun a i jm hi hj => ?_⟩
  · have mi := (mem_iff _ _).2 hi
    have mj := (mem_iff _ _).2 hj
    exact bv_trans hβ.2.1 hβ₀.2.1 a (ψp a) (hΨ a) mi.1 mi.2 mj.1 mj.2
  · have h1 : rpt (1 : Over.mk y.x ⟶ Xo.univ.t.G) ≫ conj y.x z.x ψ = rpt (1 : Over.mk z.x ⟶ Xo.univ.t.G) := by
      exact (hΨ 1).trans (congrArg (fun q => rpt q) (map_one ψp))
    exact bv_rig hβ hβ₀ h1 i j ((mem_iff _ _).2 hi) ((mem_iff _ _).2 hj)
  · have hfun : (fun w => rpt (e w)) = fun w => fibPt Xo.univ.t.G (e w) ≫ (swap y.x).inv :=
      funext fun w => (Iso.eq_comp_inv _).2 (fibPt_swap (e w))
    have hh : IsHolTo Set.univ (fun w => rpt (e w)) := by
      rw [hfun]
      exact (GlobalTheory.HolFibre.isHolTo_fibPt_and_comp _ Xo.univ.t.G y.x g e he).2 _ (swap y.x).inv
    exact bv_hol hβ.2.1 hβ₀.2.1 ψp hΨ e hh i j
  · exact bv_values hβ.2.1 hβ₀.2.1 hc₀ cr (fun m => hr.1 m) hv a (ψp a) (hΨ a) i jm ((mem_iff _ _).2 hi)
      (fun m => (mem_iff _ _).2 (hj m))

end GlobalTheory.HeckeValues
