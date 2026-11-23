import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeD

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S]

theorem tvOf_tv {x : Sp S ⟶ Xo.X} (n : TanM x Xo.univ.t.G) :
    tvOf (isTanAtG_of (t := Xo.univ.t) (x0 := x) (tv n) (tv_mem n)) = n := by
  apply tanM_ext
  first
    | rfl
    | exact Over.OverMorphism.ext rfl
    | (ext; rfl)
    | (ext1; simp [tvOf, tv, mkT])
    | simp [tvOf, tv, mkT]

theorem eig_coords (y : FrPt Xo c S) (τ : E →+* ℂ) (n : TanM y.x Xo.univ.t.G)
    (hn : IsEigV (actR (x0 := y.x) (S := S) Xo.univ.t.act) (embK c τ) n) :
    ∃! a : Fin (Dw.mult τ) → S, n = ∑ i, a i • tvOf (y.tan τ i) := by
  have hw := isTanAtG_of (t := Xo.univ.t) (x0 := y.x) (tv n) (tv_mem n)
  have hE := (eigAt_iff c hw τ).2 (by rw [tvOf_tv]; exact hn)
  obtain ⟨a, ha, huniq⟩ := y.basis τ _ hw hE
  refine ⟨a, ?_, fun a' h' => huniq a' ((combAt_iff (y.u τ) (y.tan τ) a' hw).2 ?_)⟩
  · have h1 := (combAt_iff (y.u τ) (y.tan τ) a hw).1 ha
    rw [tvOf_tv] at h1
    exact h1
  · rw [tvOf_tv]
    exact h'

theorem eig_comb {x : Sp S ⟶ Xo.X} (τ : E →+* ℂ) {m : ℕ} (v : Fin m → TanM x Xo.univ.t.G)
    (hv : ∀ i, IsEigV (actR (x0 := x) (S := S) Xo.univ.t.act) (embK c τ) (v i)) (a : Fin m → S) :
    IsEigV (actR (x0 := x) (S := S) Xo.univ.t.act) (embK c τ) (∑ i, a i • v i) := by
  intro b
  rw [map_sum]
  refine (Finset.sum_congr rfl fun i _ => ?_).trans Finset.smul_sum.symm
  rw [map_smul, hv i b]
  exact smul_comm _ _ _

def fullB (y : FrPt Xo c S) : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) → TanM y.x Xo.univ.t.G :=
  fun k => tvOf (y.tan k.1 k.2)

theorem fullB_eig (y : FrPt Xo c S) (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) :
    IsEigV (actR (x0 := y.x) (S := S) Xo.univ.t.act) (embK c τ) (fullB y ⟨τ, i⟩) :=
  (eigAt_iff c (y.tan τ i) τ).1 (y.eig τ i)

theorem fullB_basis (y : FrPt Xo c S) (m : TanM y.x Xo.univ.t.G) :
    ∃! a : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) → S, m = ∑ k, a k • fullB y k := by
  classical
  have : CharZero c.F := RingHom.charZero c.F.val.toRingHom
  obtain ⟨α, hinj, ⟨f, hf, hfs⟩, hN⟩ :=
    exists_sepElt (E := E) (F := c.F) c.F.val.toRingHom (embK c) (fun τ a => embK_coe c τ a)
  let ρ := actR (x0 := y.x) (S := S) Xo.univ.t.act
  have hsum : ∑ τ, proj ρ (embK c) α τ m = m := by
    have := congrArg (fun e : Module.End S (TanM y.x Xo.univ.t.G) => e m) (sum_proj ρ (embK c) α hinj)
    simpa [LinearMap.sum_apply] using this
  have hE : ∀ τ, IsEigV ρ (embK c τ) (proj ρ (embK c) α τ m) := fun τ =>
    eig_of_alpha ρ (embK c) α hN τ (proj_eig_alpha ρ (embK c) α hinj f hf hfs τ m)
  choose a ha hu using fun τ => eig_coords y τ (proj ρ (embK c) α τ m) (hE τ)
  refine ⟨fun k => a k.1 k.2, ?_, fun b hb => ?_⟩
  · show m = ∑ k : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), a k.1 k.2 • fullB y k
    rw [Fintype.sum_sigma]
    conv_lhs => rw [← hsum]
    exact Finset.sum_congr rfl fun τ _ => ha τ
  · have hb' : m = ∑ k : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), b k • fullB y k := hb
    rw [Fintype.sum_sigma] at hb'
    funext k
    obtain ⟨τ, i⟩ := k
    have hn := proj_sum_eig ρ (embK c) α hinj (fun τ => ∑ i, b ⟨τ, i⟩ • fullB y ⟨τ, i⟩)
      (fun τ => eig_comb τ _ (fun i => fullB_eig y τ i) _) τ
    rw [← hb'] at hn
    have := hu τ (fun i => b ⟨τ, i⟩) hn
    exact congrFun this i

end ReciprocityTheory.ChartRestriction.G.PullbackSections
