import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepLatZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeE

set_option autoImplicit false

noncomputable section

open NumberField GlobalTheory.ShFam.Pad AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EigLetters

section Tan

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} {t : SAB H X0}
  {S : Type} [CommRing S] {x0 : Sp S ⟶ X0}

def tvG {v : Sp (DualNumber S) ⟶ t.G.left} (hv : IsTanAtG t x0 v) : TanM x0 t.G :=
  mkT (ovT hv) (smT_zero_ovT hv)

theorem tv_tvG {v : Sp (DualNumber S) ⟶ t.G.left} (hv : IsTanAtG t x0 v) : tv (tvG hv) = ovT hv := rfl

theorem tvG_tv (n : TanM x0 t.G) : tvG (isTanAtG_of (t := t) (x0 := x0) (tv n) (tv_mem n)) = n :=
  tanM_ext (Over.OverMorphism.ext rfl)

theorem tv_sumG {κ : Type} (s : Finset κ) (f : κ → TanM x0 t.G) : tv (∑ i ∈ s, f i) = ∏ i ∈ s, tv (f i) := by
  simp only [tv, toMul_sum, Subgroup.val_finset_prod]

theorem combG_iff {m : ℕ} (u : Fin m → (Sp (DualNumber S) ⟶ t.G.left)) (hu : ∀ i, IsTanAtG t x0 (u i))
    (cf : Fin m → S) {w : Sp (DualNumber S) ⟶ t.G.left} (hw : IsTanAtG t x0 w) :
    IsCombAtG t x0 u cf w ↔ tvG hw = ∑ i, cf i • tvG (hu i) := by
  have e : IsCombAtG t x0 u cf w ↔ (combT x0 (fun i => ovT (hu i)) cf).left = w :=
    isCombAtG_iff t x0 (fun i => ovT (hu i)) cf w
  rw [e]
  constructor
  · intro h
    apply tanM_ext
    rw [tv_sumG, tv_tvG]
    apply Over.OverMorphism.ext
    exact h.symm
  · intro h
    have h3 : ovT hw = combT x0 (fun i => ovT (hu i)) cf := by
      rw [← tv_tvG hw, h, tv_sumG]
      rfl
    exact (congrArg (fun V => Over.Hom.left V) h3).symm

end Tan

section Letters

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H)

theorem letters_nodup : (letters Dw).Nodup := by
  unfold letters
  rw [List.nodup_flatMap]
  refine ⟨fun a _ => (List.nodup_finRange _).map (fun i j h => ?_), ?_⟩
  · simpa using h
  · refine (List.nodup_finRange _).pairwise_of_forall_ne fun a _ b _ hab => ?_
    intro x hxa hxb
    simp only [List.mem_map, List.mem_finRange, true_and] at hxa hxb
    obtain ⟨i, rfl⟩ := hxa
    obtain ⟨j, hj⟩ := hxb
    have := congrArg Sigma.fst hj
    exact hab ((Fintype.equivFin (E →+* ℂ)).symm.injective this.symm)

theorem mem_letters (x : Letter Dw) : x ∈ letters Dw := by
  obtain ⟨τ, i⟩ := x
  unfold letters
  refine List.mem_flatMap.2 ⟨Fintype.equivFin (E →+* ℂ) τ, List.mem_finRange _, ?_⟩
  generalize hσ : (Fintype.equivFin (E →+* ℂ)).symm (Fintype.equivFin (E →+* ℂ) τ) = σ
  obtain rfl : σ = τ := by rw [← hσ, Equiv.symm_apply_apply]
  exact List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩

end Letters

section Flag

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {Ω : Type} [Field Ω] [Algebra c.F Ω] (y : FlagPt Z Ω) (hA : algebraMap c.F Ω = y.fK)

include hA in
theorem eig_iffG (τ : E →+* ℂ) {w : Sp (DualNumber Ω) ⟶ Z.t.G.left} (hw : IsTanAtG Z.t (y.y ≫ GlobalTheory.Toroidal.genι Z) w) :
    (∀ a : 𝓞 E, w ≫ (Z.t.act.act a).left = spMap (epsMul (y.fK (embF c τ (a : E)))) ≫ w) ↔
      IsEigV (actR (x0 := y.y ≫ GlobalTheory.Toroidal.genι Z) (S := Ω) Z.t.act) (embK c τ) (tvG hw) := by
  rw [← hA]
  refine forall_congr' fun a => ⟨fun h => tanM_ext ?_, fun h => ?_⟩
  · apply Over.OverMorphism.ext
    exact h
  · have := congrArg (fun V => (tv V).left) h
    exact this

include hA in
theorem eig_coordsG (τ : E →+* ℂ) (n : TanM (y.y ≫ GlobalTheory.Toroidal.genι Z) Z.t.G)
    (hn : IsEigV (actR (x0 := y.y ≫ GlobalTheory.Toroidal.genι Z) (S := Ω) Z.t.act) (embK c τ) n) :
    ∃! a : Fin (Dw.mult τ) → Ω, n = ∑ i, a i • tvG (y.tan τ i) := by
  have hw := isTanAtG_of (t := Z.t) (x0 := y.y ≫ GlobalTheory.Toroidal.genι Z) (tv n) (tv_mem n)
  have heig := (eig_iffG y hA τ hw).2 ((tvG_tv n).symm ▸ hn)
  obtain ⟨a, ha, hu⟩ := y.basis τ _ hw heig
  refine ⟨a, ?_, fun b hb => hu b ?_⟩
  · rw [← tvG_tv n]
    exact (combG_iff (y.u τ) (y.tan τ) a hw).1 ha
  · refine (combG_iff (y.u τ) (y.tan τ) b hw).2 ?_
    rw [tvG_tv n]
    exact hb

theorem eig_combG {x : Sp Ω ⟶ Z.X} (τ : E →+* ℂ) {m : ℕ} (v : Fin m → TanM x Z.t.G)
    (hv : ∀ i, IsEigV (actR (x0 := x) (S := Ω) Z.t.act) (embK c τ) (v i)) (a : Fin m → Ω) :
    IsEigV (actR (x0 := x) (S := Ω) Z.t.act) (embK c τ) (∑ i, a i • v i) := by
  intro b
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, hv i b, smul_comm]

def fullG : Letter Dw → TanM (y.y ≫ GlobalTheory.Toroidal.genι Z) Z.t.G := fun k => tvG (y.tan k.1 k.2)

include hA in
theorem fullG_eig (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) :
    IsEigV (actR (x0 := y.y ≫ GlobalTheory.Toroidal.genι Z) (S := Ω) Z.t.act) (embK c τ) (fullG y ⟨τ, i⟩) :=
  (eig_iffG y hA τ (y.tan τ i)).1 (y.eig τ i)

include hA in
theorem fullG_basis (m : TanM (y.y ≫ GlobalTheory.Toroidal.genι Z) Z.t.G) :
    ∃! a : Letter Dw → Ω, m = ∑ k, a k • fullG y k := by
  classical
  have : CharZero c.F := RingHom.charZero c.F.val.toRingHom
  obtain ⟨α, hinj, ⟨f, hf, hfs⟩, hN⟩ :=
    exists_sepElt (E := E) (F := c.F) c.F.val.toRingHom (embK c) (fun τ a => embK_coe c τ a)
  let ρ := actR (x0 := y.y ≫ GlobalTheory.Toroidal.genι Z) (S := Ω) Z.t.act
  have hsum : ∑ τ, proj ρ (embK c) α τ m = m := by
    have := congrArg (fun e : Module.End Ω (TanM (y.y ≫ GlobalTheory.Toroidal.genι Z) Z.t.G) => e m)
      (sum_proj ρ (embK c) α hinj)
    simpa [LinearMap.sum_apply] using this
  have hE : ∀ τ, IsEigV ρ (embK c τ) (proj ρ (embK c) α τ m) := fun τ =>
    eig_of_alpha ρ (embK c) α hN τ (proj_eig_alpha ρ (embK c) α hinj f hf hfs τ m)
  choose a ha hu using fun τ => eig_coordsG y hA τ (proj ρ (embK c) α τ m) (hE τ)
  refine ⟨fun k => a k.1 k.2, ?_, fun b hb => ?_⟩
  · show m = ∑ k : Letter Dw, a k.1 k.2 • fullG y k
    rw [Fintype.sum_sigma]
    conv_lhs => rw [← hsum]
    exact Finset.sum_congr rfl fun τ _ => ha τ
  · have hb' : m = ∑ k : Letter Dw, b k • fullG y k := hb
    rw [Fintype.sum_sigma] at hb'
    funext k
    obtain ⟨τ, i⟩ := k
    have hn := proj_sum_eig ρ (embK c) α hinj (fun τ => ∑ i, b ⟨τ, i⟩ • fullG y ⟨τ, i⟩)
      (fun τ => eig_combG τ _ (fun i => fullG_eig y hA τ i) _) τ
    rw [← hb'] at hn
    have := hu τ (fun i => b ⟨τ, i⟩) hn
    exact congrFun this i

end Flag

theorem letters_basis : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) {Ω : Type} [Field Ω] (y : GlobalTheory.ShFam.Pad.FlagPt Z Ω) (w : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (DualNumber Ω) ⟶ Z.t.G.left), Formalism.L2.Pj.IsTanAtG Z.t (y.y ≫ GlobalTheory.Toroidal.genι Z) w → ∃! a : Fin (GlobalTheory.ShFam.Pad.letters Dw).length → Ω, Formalism.L2.Pj.IsCombAtG Z.t (y.y ≫ GlobalTheory.Toroidal.genι Z) (fun k => y.u ((GlobalTheory.ShFam.Pad.letters Dw).get k).1 ((GlobalTheory.ShFam.Pad.letters Dw).get k).2) a w := by
  intro E _ _ _ H Dw l Xo c O _ β Z Ω _ y w hw
  classical
  letI : Algebra c.F Ω := y.fK.toAlgebra
  set L := GlobalTheory.ShFam.Pad.letters Dw with hL
  let e : Fin L.length ≃ Letter Dw := (letters_nodup Dw).getEquivOfForallMemList _ (mem_letters Dw)
  have he : ∀ k, e k = L.get k := fun k => rfl
  have hc : ∀ a : Fin L.length → Ω, Formalism.L2.Pj.IsCombAtG Z.t (y.y ≫ GlobalTheory.Toroidal.genι Z)
      (fun k => y.u (L.get k).1 (L.get k).2) a w ↔ tvG hw = ∑ k, a k • fullG y (e k) := fun a =>
    combG_iff (fun k => y.u (L.get k).1 (L.get k).2) (fun k => y.tan _ _) a hw
  obtain ⟨b, hb, hbu⟩ := fullG_basis y rfl (tvG hw)
  refine ⟨fun k => b (e k), (hc _).2 ?_, fun a ha => ?_⟩
  · rw [hb]
    exact (Equiv.sum_comp e (fun x => b x • fullG y x)).symm
  · have h1 := (hc a).1 ha
    have h2 : tvG hw = ∑ x, a (e.symm x) • fullG y x := by
      rw [h1, ← Equiv.sum_comp e]
      simp
    have := hbu _ h2
    funext k
    have := congrFun this (e k)
    simpa using this

end GlobalTheory.EigLetters
