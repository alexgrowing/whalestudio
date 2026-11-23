import Formalism.LocalToGlobal.GlobalTheory.GL6.FrobeniusNoKernelOfFrobeniusSimilitude

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {ι : Type} [Fintype ι]

theorem rnd_tr_tr (emb : ι → E →+* ℂ) (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x))
    (a b : GL (Fin n) E) (ha : a ∈ UJ (σ : E →+* E) J) (hb : b ∈ UJ (σ : E →+* E) J) (y : Frames (gramC J emb)) :
    frameTranslate emb hc a ha (frameTranslate emb hc b hb y) = frameTranslate emb hc (a * b) ((UJ (σ : E →+* E) J).mul_mem ha hb) y := by
  apply Subtype.ext
  funext τ
  simp only [frameTranslate, atInf, Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]

theorem rnd_tr_one (emb : ι → E →+* ℂ) (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x))
    (y : Frames (gramC J emb)) : frameTranslate emb hc 1 (UJ (σ : E →+* E) J).one_mem y = y := by
  apply Subtype.ext
  funext τ
  simp [frameTranslate, atInf]

theorem rnd_tr_congr (emb : ι → E →+* ℂ) (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x))
    {a b : GL (Fin n) E} (hab : a = b) (ha : a ∈ UJ (σ : E →+* E) J) (hb : b ∈ UJ (σ : E →+* E) J)
    (y : Frames (gramC J emb)) : frameTranslate emb hc a ha y = frameTranslate emb hc b hb y := by
  subst hab; rfl

theorem rnd_core (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ)
    (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x))
    {g G : UPts σ J (FiniteAdeleRing (𝓞 F) F) → Frames (gramC J emb) → ℂ} (hg : g ∈ AdFun S emb) (hG : G ∈ AdFun S emb)
    (xc xu η η' : UPts σ J (FiniteAdeleRing (𝓞 F) F)) (γ γ' : GL (Fin n) E)
    (hγ : γ ∈ UJ (σ : E →+* E) J) (hγ' : γ' ∈ UJ (σ : E →+* E) J) (κ κ' k : S.U)
    (hU : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * xu.1 = xc.1 * η.1 * κ.1)
    (hD : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ' * xc.1 = xu.1 * η'.1 * κ'.1)
    (hk : k.1 = η.1 * κ.1 * η'.1 * κ'.1) (hχ : S.chi k = S.chi κ * S.chi κ')
    (hfill : G xu = g (xu * η')) :
    G (xc * η) = g xc := by
  funext y
  have e1 : (xc * η).1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * xu.1 * (κ⁻¹ : S.U).1 := by
    simp only [Subgroup.coe_mul, hU, InvMemClass.coe_inv]; group
  have e2 : (xu * η').1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ' * xc.1 * (κ'⁻¹ : S.U).1 := by
    simp only [Subgroup.coe_mul, hD, InvMemClass.coe_inv]; group
  have e0 : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ' * xc.1 =
      xc.1 * k.1 := by
    rw [mul_assoc, hD, ← mul_assoc, ← mul_assoc, hU, hk]; group
  have e3 : xc.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (γ * γ') * xc.1 * (k⁻¹ : S.U).1 := by
    rw [map_mul, e0, InvMemClass.coe_inv]; group
  have hγγ : γ * γ' ∈ UJ (σ : E →+* E) J := (UJ (σ : E →+* E) J).mul_mem hγ hγ'
  have a1 := adelic_value_translate S emb hc hG γ hγ xu (xc * η) κ⁻¹ e1 y
  have a2 := adelic_value_translate S emb hc hg γ' hγ' xc (xu * η') κ'⁻¹ e2
    (frameTranslate emb hc γ⁻¹ ((UJ (σ : E →+* E) J).inv_mem hγ) y)
  have a3 := adelic_value_translate S emb hc hg (γ * γ') hγγ xc xc k⁻¹ e3 y
  rw [a1, hfill, a2, rnd_tr_tr,
    rnd_tr_congr emb hc (mul_inv_rev γ γ').symm _ ((UJ (σ : E →+* E) J).inv_mem hγγ)]
  rw [a3, map_inv, map_inv, map_inv, hχ]
  simp only [mul_inv, Units.val_mul, Units.val_inv_eq_inv_val]
  ring

end Gen

section Fill

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {ι : Type} [Fintype ι]

def RndStabTriv (S : StepLevel F E σ J T f bad) (x0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) : Prop :=
  ∀ δ : GL (Fin n) E, δ ∈ UJ (σ : E →+* E) J → ∀ κ : S.U,
    bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) δ * x0.1 = x0.1 * κ.1 → δ = 1

theorem rnd_uniq (S : StepLevel F E σ J T f bad) (x0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) (hs : RndStabTriv S x0)
    {a b : GL (Fin n) E} (ha : a ∈ UJ (σ : E →+* E) J) (hb : b ∈ UJ (σ : E →+* E) J) {k l : S.U}
    (h : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) a * x0.1 * k.1 =
      bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) b * x0.1 * l.1) : a = b ∧ k = l := by
  have hδ : b⁻¹ * a ∈ UJ (σ : E →+* E) J := (UJ (σ : E →+* E) J).mul_mem ((UJ (σ : E →+* E) J).inv_mem hb) ha
  have e : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (b⁻¹ * a) * x0.1 = x0.1 * (l * k⁻¹ : S.U).1 := by
    have h' : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) a * x0.1 =
        bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) b * x0.1 * l.1 * k.1⁻¹ := by
      rw [← h]; group
    rw [map_mul, map_inv, Subgroup.coe_mul, InvMemClass.coe_inv, mul_assoc, h']; group
  have h1 := hs _ hδ _ e
  have hab : a = b := (inv_mul_eq_one.1 h1).symm
  subst hab
  exact ⟨rfl, Subtype.ext (mul_left_cancel h)⟩

open Classical in

def rndFillG (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ) (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x))
    (x0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) (h : Frames (gramC J emb) → ℂ) :
    UPts σ J (FiniteAdeleRing (𝓞 F) F) → Frames (gramC J emb) → ℂ := fun x y =>
  if hx : ∃ p : {γ : GL (Fin n) E // γ ∈ UJ (σ : E →+* E) J} × S.U,
      x.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) p.1.1 * x0.1 * p.2.1 then
    (S.chi (Classical.choose hx).2 : ℂ) *
      h (frameTranslate emb hc (Classical.choose hx).1.1⁻¹ ((UJ (σ : E →+* E) J).inv_mem (Classical.choose hx).1.2) y)
  else 0

theorem rnd_fillG_eq (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ)
    (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x))
    (x0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) (hs : RndStabTriv S x0) (h : Frames (gramC J emb) → ℂ)
    (x : UPts σ J (FiniteAdeleRing (𝓞 F) F)) (p : {γ : GL (Fin n) E // γ ∈ UJ (σ : E →+* E) J} × S.U)
    (hp : x.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) p.1.1 * x0.1 * p.2.1) (y : Frames (gramC J emb)) :
    rndFillG S emb hc x0 h x y =
      (S.chi p.2 : ℂ) * h (frameTranslate emb hc p.1.1⁻¹ ((UJ (σ : E →+* E) J).inv_mem p.1.2) y) := by
  have hx : ∃ p : {γ : GL (Fin n) E // γ ∈ UJ (σ : E →+* E) J} × S.U,
      x.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) p.1.1 * x0.1 * p.2.1 := ⟨p, hp⟩
  unfold rndFillG
  rw [dif_pos hx]
  have hq := Classical.choose_spec hx
  have hu := rnd_uniq S x0 hs (Classical.choose hx).1.2 p.1.2 (k := (Classical.choose hx).2) (l := p.2)
    (by rw [← hq, ← hp])
  have hpq : Classical.choose hx = p := Prod.ext (Subtype.ext hu.1) hu.2
  exact congrArg (fun q : {γ : GL (Fin n) E // γ ∈ UJ (σ : E →+* E) J} × S.U =>
    (S.chi q.2 : ℂ) * h (frameTranslate emb hc q.1.1⁻¹ ((UJ (σ : E →+* E) J).inv_mem q.1.2) y)) hpq

theorem rnd_fillG_eq' (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ)
    (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x))
    (x0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) (hs : RndStabTriv S x0) (h : Frames (gramC J emb) → ℂ)
    (x : UPts σ J (FiniteAdeleRing (𝓞 F) F)) (a : GL (Fin n) E) (ha : a ∈ UJ (σ : E →+* E) J) (k : S.U)
    (hp : x.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) a * x0.1 * k.1) (y : Frames (gramC J emb)) :
    rndFillG S emb hc x0 h x y = (S.chi k : ℂ) * h (frameTranslate emb hc a⁻¹ ((UJ (σ : E →+* E) J).inv_mem ha) y) :=
  rnd_fillG_eq S emb hc x0 hs h x (⟨a, ha⟩, k) hp y

theorem rnd_fill_at (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ)
    (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x))
    (x0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) (hs : RndStabTriv S x0) (h : Frames (gramC J emb) → ℂ) :
    rndFillG S emb hc x0 h x0 = h := by
  funext y
  rw [rnd_fillG_eq S emb hc x0 hs h x0 (⟨1, (UJ (σ : E →+* E) J).one_mem⟩, 1) (by simp) y, map_one, Units.val_one,
    one_mul, rnd_tr_congr emb hc (inv_one) _ (UJ (σ : E →+* E) J).one_mem, rnd_tr_one]

open Classical in
theorem rnd_fill_mem (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ)
    (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x))
    (x0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) (hs : RndStabTriv S x0) (h : Frames (gramC J emb) → ℂ) :
    rndFillG S emb hc x0 h ∈ AdFun S emb := by
  intro γ hγ x x' κ hx y y' hy
  have hy' : y' = frameTranslate emb hc γ⁻¹ ((UJ (σ : E →+* E) J).inv_mem hγ) y := by
    apply Subtype.ext; funext τ
    show y'.1 τ = atInf emb ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ * y.1 τ
    rw [hy τ, ← Matrix.mul_assoc]
    simp only [atInf]
    rw [← Matrix.map_mul, Units.inv_mul]; simp
  by_cases h1 : ∃ p : {γ : GL (Fin n) E // γ ∈ UJ (σ : E →+* E) J} × S.U,
      x.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) p.1.1 * x0.1 * p.2.1
  · obtain ⟨p, hp⟩ := h1
    have hp' : x'.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (γ * p.1.1) * x0.1 * (p.2 * κ).1 := by
      simp only [hx, hp, map_mul, Subgroup.coe_mul]; group
    rw [rnd_fillG_eq' S emb hc x0 hs h x' (γ * p.1.1) ((UJ (σ : E →+* E) J).mul_mem hγ p.1.2) (p.2 * κ) hp' y, rnd_fillG_eq S emb hc x0 hs h x p hp y', map_mul, Units.val_mul,
      rnd_tr_congr emb hc (mul_inv_rev γ p.1.1) _
        ((UJ (σ : E →+* E) J).mul_mem ((UJ (σ : E →+* E) J).inv_mem p.1.2) ((UJ (σ : E →+* E) J).inv_mem hγ)),
      ← rnd_tr_tr, ← hy']
    ring
    · exact (UJ (σ : E →+* E) J).inv_mem p.1.2
    · exact (UJ (σ : E →+* E) J).inv_mem hγ
  · have h2 : ¬ ∃ p : {γ : GL (Fin n) E // γ ∈ UJ (σ : E →+* E) J} × S.U,
        x'.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) p.1.1 * x0.1 * p.2.1 := by
      rintro ⟨p, hp⟩
      refine h1 ⟨(⟨γ⁻¹ * p.1.1, (UJ (σ : E →+* E) J).mul_mem ((UJ (σ : E →+* E) J).inv_mem hγ) p.1.2⟩, p.2 * κ⁻¹), ?_⟩
      have : x.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ⁻¹ * x'.1 * κ.1⁻¹ := by rw [hx, map_inv]; group
      rw [this, hp, map_mul, map_inv, Subgroup.coe_mul, InvMemClass.coe_inv]; group
    unfold rndFillG
    rw [dif_neg h1, dif_neg h2, mul_zero]

theorem rnd_fill (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ)
    (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x))
    (x0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) (hs : RndStabTriv S x0) (h : Frames (gramC J emb) → ℂ) :
    ∃ G ∈ AdFun S emb, G x0 = h :=
  ⟨rndFillG S emb hc x0 h, rnd_fill_mem S emb hc x0 hs h, rnd_fill_at S emb hc x0 hs h⟩

end Fill

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
