import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenScal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCoverComponentOverBaseRationalIsometry
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticGroupConjIsometryMovesCoverPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionPullbackExistsUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal

noncomputable section

namespace GlobalTheory.LevModel

section Group

theorem nonempty_equiv_sigma_quotient {T K G : Type*} [Group G] (Hs : K → Subgroup G) (P : T → K → G → Prop)
    (ex : ∀ y, ∃ k g, P y k g) (w₁ : ∀ y k k' g g', P y k g → P y k' g' → k = k')
    (w₂ : ∀ y k g g', P y k g → P y k g' → g⁻¹ * g' ∈ Hs k)
    (inj : ∀ y y' k g g', P y k g → P y' k g' → g⁻¹ * g' ∈ Hs k → y = y')
    (surj : ∀ k g, ∃ y, P y k g) : Nonempty (T ≃ Σ k, G ⧸ Hs k) := by
  choose kk gg hP using ex
  have val : ∀ y k g, P y k g → (⟨kk y, (gg y : G ⧸ Hs (kk y))⟩ : Σ k, G ⧸ Hs k) = ⟨k, (g : G ⧸ Hs k)⟩ := by
    intro y k g h
    obtain rfl := w₁ y _ _ _ _ (hP y) h
    exact congrArg _ (QuotientGroup.eq.2 (w₂ y _ _ _ (hP y) h))
  refine ⟨Equiv.ofBijective (fun y => ⟨kk y, (gg y : G ⧸ Hs (kk y))⟩) ⟨fun y y' e => ?_, ?_⟩⟩
  · have key : ∀ k (g : G), P y' k g → (⟨kk y, (gg y : G ⧸ Hs (kk y))⟩ : Σ k, G ⧸ Hs k) = ⟨k, (g : G ⧸ Hs k)⟩ → y = y' := by
      intro k g h e'
      obtain ⟨rfl, e₂⟩ := Sigma.mk.inj_iff.1 e'
      exact inj _ _ _ _ _ (hP y) h (QuotientGroup.eq.1 (eq_of_heq e₂))
    exact key _ _ (hP y') e
  · rintro ⟨k, q⟩
    induction q using QuotientGroup.induction_on with
    | H g =>
      obtain ⟨y, hy⟩ := surj k g
      exact ⟨y, val y k g hy⟩

end Group

section Frames

open ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem exists_moved {X₂ X : Data E r} (hΨ : X₂.Ψ = X.Ψ) (δ : GL (Fin r) E) (x : Frame X₂.Ψ r) :
    ∃ x', Moved X₂ X δ x x' :=
  ⟨fun τ => ((δ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x ⟨τ.1, by rw [hΨ]; exact τ.2⟩ : Matrix (Fin r) (Fin r) ℂ),
    fun _ _ _ => rfl⟩

omit [NumberField E] [IsCMField E] in
theorem map_mul_map_inv (τ : E →+* ℂ) (δ : GL (Fin r) E) :
    (δ : Matrix (Fin r) (Fin r) E).map τ * ((δ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ = 1 := by
  rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  exact Matrix.map_one _ (map_zero τ) (map_one τ)

omit [NumberField E] [IsCMField E] in
theorem map_inv_mul_map (τ : E →+* ℂ) (δ : GL (Fin r) E) :
    ((δ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ * (δ : Matrix (Fin r) (Fin r) E).map τ = 1 := by
  rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  exact Matrix.map_one _ (map_zero τ) (map_one τ)

theorem exists_moved_back {X₂ X : Data E r} (hΨ : X₂.Ψ = X.Ψ) (δ : GL (Fin r) E) (x' : Frame X.Ψ r) :
    ∃ x, Moved X₂ X δ x x' :=
  ⟨fun τ => (((δ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x' ⟨τ.1, hΨ ▸ τ.2⟩ : Matrix (Fin r) (Fin r) ℂ),
    fun τ _ h₁ => by
      show mat x' ⟨τ, h₁⟩ = (δ : Matrix (Fin r) (Fin r) E).map τ *
        (((δ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ * mat x' ⟨τ, h₁⟩)
      rw [← Matrix.mul_assoc, map_mul_map_inv, Matrix.one_mul]⟩

theorem mem_dom_of_moved {X₂ X : Data E r} (δ : GL (Fin r) E) (hp : X₂.p0 = X.p0) (hΨ : X₂.Ψ = X.Ψ) (hG : X₂.Gm = X.Gm)
    (hiso : ∀ v w, herm X₂.Gm ((δ : Matrix (Fin r) (Fin r) E).mulVec v) ((δ : Matrix (Fin r) (Fin r) E).mulVec w) =
      herm X₂.Gm v w)
    {x : Frame X₂.Ψ r} {x' : Frame X.Ψ r} (hm : Moved X₂ X δ x x') (hx' : x' ∈ X.dom) : x ∈ X₂.dom := by
  refine GlobalTheory.FrameDom.mem_dom_of_isometry E r X₂ X δ⁻¹ hp (fun τ => by rw [hΨ]) (fun v w => ?_) x' x hx' fun τ h₂ h₁ => ?_
  · have e : ∀ u : Fin r → E, (δ : Matrix (Fin r) (Fin r) E).mulVec
        (((δ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).mulVec u) = u := fun u => by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    have h := hiso (((δ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).mulVec v)
      (((δ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).mulVec w)
    rw [e, e] at h
    rw [← h, hG]
  · rw [hm τ h₁ h₂, ← Matrix.mul_assoc, map_inv_mul_map, Matrix.one_mul]

theorem moved_iff {Ψ₂ Ψ : Finset (E →+* ℂ)} (h : Ψ₂ = Ψ) (δ g : GL (Fin r) E) {x₂ x₂' : Frame Ψ₂ r} {x₁ x₁' : Frame Ψ r}
    (m : ∀ (τ : E →+* ℂ) (h₂ : τ ∈ Ψ₂) (h₁ : τ ∈ Ψ),
      mat x₁ ⟨τ, h₁⟩ = (δ : Matrix (Fin r) (Fin r) E).map τ * mat x₂ ⟨τ, h₂⟩)
    (m' : ∀ (τ : E →+* ℂ) (h₂ : τ ∈ Ψ₂) (h₁ : τ ∈ Ψ),
      mat x₁' ⟨τ, h₁⟩ = (δ : Matrix (Fin r) (Fin r) E).map τ * mat x₂' ⟨τ, h₂⟩) :
    (∃ b ∈ Bor Ψ₂ r, x₂' = rmul (lact g x₂) b) ↔ ∃ b ∈ Bor Ψ r, x₁' = rmul (lact (MulAut.conj δ g) x₁) b := by
  subst h
  obtain rfl : x₁ = lact δ x₂ := funext fun τ => m τ.1 τ.2 τ.2
  obtain rfl : x₁' = lact δ x₂' := funext fun τ => m' τ.1 τ.2 τ.2
  have e : lact (MulAut.conj δ g) (lact δ x₂) = lact δ (lact g x₂) := by
    rw [← lact_mul, ← lact_mul, MulAut.conj_apply, inv_mul_cancel_right]
  rw [e]
  refine exists_congr fun b => and_congr_right fun _ => ?_
  rw [← lact_rmul δ (lact g x₂) b]
  constructor
  · exact fun h => congrArg _ h
  · intro h
    have := congrArg (lact δ⁻¹) h
    rwa [lact_inv, lact_inv] at this

theorem eq_rmul_lact (X : Data E r) {γ γ' : GL (Fin r) E} {x y b b' : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r)
    (e : rmul (lact γ x) b = rmul (lact γ' y) b') : x = rmul (lact (γ⁻¹ * γ') y) (rmul b' (invF X b)) := by
  have h₁ : lact γ⁻¹ (rmul (lact γ x) b) = rmul x b := by rw [lact_rmul, lact_inv]
  have h₂ : lact γ⁻¹ (rmul (lact γ' y) b') = rmul (lact (γ⁻¹ * γ') y) b' := by rw [lact_rmul, ← lact_mul]
  have h₃ : rmul x b = rmul (lact (γ⁻¹ * γ') y) b' := by rw [← h₁, e, h₂]
  calc x = rmul (rmul x b) (invF X b) := by rw [rmul_assoc, rmul_invF X hb, rmul_oneF]
    _ = _ := by rw [h₃, rmul_assoc]

theorem eq_of_rmul_lact_eq (X : Data E r) {γ γ' : GL (Fin r) E} (hγ : γ ∈ X.Γ) (hγ' : γ' ∈ X.Γ) {x b b' : Frame X.Ψ r}
    (hx : x ∈ X.dom) (hb : b ∈ Bor X.Ψ r) (hb' : b' ∈ Bor X.Ψ r)
    (e : rmul (lact γ x) b = rmul (lact γ' x) b') : γ = γ' := by
  have h := eq_rmul_lact X hb' e.symm
  have hc : rmul b (invF X b') ∈ Bor X.Ψ r := mul_mem X hb (invF_mem X hb')
  set c := rmul b (invF X b') with hcd
  have e₂ : lact (γ'⁻¹ * γ) x = rmul x (invF X c) := by
    conv_rhs => rw [h]
    rw [rmul_assoc, rmul_invF X hc, rmul_oneF]
  have h₁ := X.Γ_free _ (X.Γ.mul_mem (X.Γ.inv_mem hγ') hγ) x hx _ (invF_mem X hc) e₂
  exact (inv_mul_eq_one.1 h₁).symm

end Frames

section Lift

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.FrameLift

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ}

theorem frOver_inj (d : DeltaDat Xo c n) (hG : GlobalFnsSt) {S : Type} [CommRing S] [Algebra c.F S] [Algebra d.c₂.F S]
    {y : FrPt Xo c S} {y₂ y₂' : FrPt d.Xo₂ d.c₂ S} (h : FrOver d y₂ y) (h' : FrOver d y₂' y) (ex : y₂.x = y₂'.x) :
    y₂ = y₂' := by
  obtain ⟨e, hu, w, p, hw, p₁, p₂, R⟩ := (frOver_iff d _ _).1 h
  obtain ⟨e', hu', w', p', hw', p₁', p₂', R'⟩ := (frOver_iff d _ _).1 h'
  obtain rfl : w = w' := rigidified_iso_unique hG (UnivPol.pol d.Xo₂) Xo.univ.t.PP.isLB d.m.φ w w' hw.1 hw'.1 _ _
    hw.2 hw'.2
  obtain ⟨x, xo, u, tan, eig, bas, s, gen⟩ := y₂
  obtain ⟨x', xo', u', tan', eig', bas', s', gen'⟩ := y₂'
  dsimp only at ex e e' hu hu' p p₁ p₂ R p' p₁' p₂' R'
  subst ex
  obtain rfl : u = u' := funext fun τ => funext fun i =>
    d.m.cart.1.hom_ext ((hu τ i).trans (hu' τ i).symm) ((tan τ i).1.trans (tan' τ i).1.symm)
  obtain rfl : p = p' := pm_ext (p₁.trans p₁'.symm) (p₂.trans p₂'.symm)
  obtain ⟨p'', n', q₁, q₂, hn, -⟩ := exists_pm_iso d.m e
  obtain rfl : p'' = p := pm_ext (q₁.trans p₁.symm) (q₂.trans p₂.symm)
  have one : ∀ {Z Y : Scheme.{0}} (r : Z ⟶ Y) (z : Z), ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs r z ⊤ (1 : Γ(Y, ⊤)) = 1 := fun r z => by
    rw [gs_eq r z ⊤ (by trivial), map_one, map_one]
  have K := (rel_scal_iff Xo.univ.t.PP.isLB d.Xo₂.univ.t.PP.isLB p₁ hn p₂ (1 : Γ(Sp S, ⊤)) R R').2 (fun Z r z j _ => by
    rw [one, _root_.one_mul])
  have K₂ := (scal_iff (fst (Over.mk x) d.Xo₂.univ.t.G).left (1 : Γ(Sp S, ⊤)) s s').2 K
  obtain rfl : s = s' := by
    cases s
    cases s'
    congr
    funext i
    have k := K₂ i
    simp only [map_one] at k
    exact (k.trans (_root_.one_mul _)).symm
  rfl

end Lift

section Core

open CategoryTheory GlobalTheory.FrameLift ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem lifts_equiv (d : DeltaDat Xo c 0) (σ₂ : d.c₂.F →+* ℂ) {r : ℕ}
    (B : Unf Xo c (σ₂.comp (d.eF : c.F →+* d.c₂.F)) r) (C : Unf d.Xo₂ d.c₂ σ₂ r) (hB : IsUnf B) (hC : IsUnf C)
    (π : C.Comp → B.Comp) (δ : C.Comp → GL (Fin r) E) (hGm : ∀ k₂, (C.X k₂).Gm = (B.X (π k₂)).Gm)
    (hiso : ∀ k₂ v w, herm (C.X k₂).Gm (((δ k₂) : Matrix (Fin r) (Fin r) E).mulVec v)
      (((δ k₂) : Matrix (Fin r) (Fin r) E).mulVec w) = herm (C.X k₂).Gm v w)
    (hle : ∀ k₂, (C.X k₂).Γ.map (MulAut.conj (δ k₂)).toMonoidHom ≤ (B.X (π k₂)).Γ)
    (hOv : ∀ k₂, Over d σ₂ B C k₂ (π k₂) (δ k₂)) (k : B.Comp) (x' : (B.X k).dom) :
    letI : Algebra c.F (CAt σ₂) := (σ₂.comp (d.eF : c.F →+* d.c₂.F)).toAlgebra
    Nonempty ({y₂ : FrPt d.Xo₂ d.c₂ (CAt σ₂) // FrOver d y₂ (B.un k x')} ≃
      Σ k₂ : {k₂ // π k₂ = k}, ↥(B.X k).Γ ⧸ (((C.X k₂.1).Γ.map (MulAut.conj (δ k₂.1)).toMonoidHom).subgroupOf (B.X k).Γ)) := by
  letI : Algebra c.F (CAt σ₂) := (σ₂.comp (d.eF : c.F →+* d.c₂.F)).toAlgebra
  have hG := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  have G := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid _ H Dw l Xo c (CAt σ₂)
  have G₂ := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid _ H Dw d.l₂ d.Xo₂ d.c₂ (CAt σ₂)
  have hΨ : ∀ k₂ k, (C.X k₂).Ψ = (B.X k).Ψ := fun k₂ k => Finset.ext fun τ =>
    ((hC.2.1 k₂).2 τ).trans ((hB.2.1 k).2 τ).symm
  have hp : ∀ k₂ k, (C.X k₂).p0 = (B.X k).p0 := fun k₂ k => (hC.2.1 k₂).1.trans (hB.2.1 k).1.symm
  refine nonempty_equiv_sigma_quotient _ (fun y k₂ γ => ∃ (x₂ : (C.X k₂.1).dom) (t : Ix Dw → (CAt σ₂)ˣ)
      (x₁ : Frame (B.X k).Ψ r), ∃ b ∈ Bor (B.X k).Ψ r, FrBor t (C.un k₂.1 x₂) y.1 ∧
        Moved (C.X k₂.1) (B.X k) (δ k₂.1) x₂.1 x₁ ∧ x'.1 = rmul (lact γ.1 x₁) b) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨y₂, hy⟩
    obtain ⟨k₂, x₂, t, ht⟩ := hC.2.2.1 y₂
    obtain ⟨x₁, hm⟩ := exists_moved (hΨ k₂ (π k₂)) (δ k₂) x₂.1
    obtain ⟨hx₁, s, -, y₀, hb₀, ho⟩ := hOv k₂ x₂.1 x₂.2 x₁ hm
    have hb := GlobalTheory.CoverSec.frBor_down d hG ho hy ht
    have hc := G.2.1 _ _ _ _ _ hb₀ hb
    obtain ⟨γ, hγ, b, hb', e⟩ := (hB.2.2.2.1 (π k₂) k ⟨x₁, hx₁⟩ x').1 ⟨_, hc⟩
    obtain ⟨hk, e₂⟩ := Sigma.mk.inj_iff.1 e
    subst hk
    exact ⟨⟨k₂, rfl⟩, ⟨γ, hγ⟩, x₂, t, x₁, b, hb', ht, hm, eq_of_heq e₂⟩
  · rintro ⟨y₂, hy⟩ ⟨k₂, hk⟩ ⟨k₂', hk'⟩ γ γ' ⟨x₂, t, x₁, b, hb, ht, hm, e⟩ ⟨x₂', t', x₁', b', hb', ht', hm', e'⟩
    have hc := G₂.2.1 _ _ _ _ _ ht (G₂.2.2.1 _ _ _ ht')
    obtain ⟨g, hg, b₂, hb₂, e₂⟩ := (hC.2.2.2.1 k₂ k₂' x₂ x₂').1 ⟨_, hc⟩
    exact Subtype.ext (Sigma.mk.inj_iff.1 e₂).1.symm
  · rintro ⟨y₂, hy⟩ ⟨k₂, hk⟩ γ γ' ⟨x₂, t, x₁, b, hb, ht, hm, e⟩ ⟨x₂', t', x₁', b', hb', ht', hm', e'⟩
    subst hk
    have hc := G₂.2.1 _ _ _ _ _ ht (G₂.2.2.1 _ _ _ ht')
    obtain ⟨g, hg, b₂, hb₂, e₂⟩ := (hC.2.2.2.1 k₂ k₂ x₂ x₂').1 ⟨_, hc⟩
    have e₃ : x₂'.1 = rmul (lact g x₂.1) b₂ := eq_of_heq (Sigma.mk.inj_iff.1 e₂).2
    obtain ⟨b₃, hb₃, e₄⟩ := (moved_iff (hΨ k₂ (π k₂)) (δ k₂) g hm hm').1 ⟨b₂, hb₂, e₃⟩
    have hh : MulAut.conj (δ k₂) g ∈ (B.X (π k₂)).Γ := hle k₂ (Subgroup.mem_map.2 ⟨g, hg, rfl⟩)
    obtain ⟨hx₁, -⟩ := hOv k₂ x₂.1 x₂.2 x₁ hm
    have e₅ : rmul (lact γ.1 x₁) b = rmul (lact (γ'.1 * MulAut.conj (δ k₂) g) x₁) (rmul b₃ b') := by
      rw [← e, e', e₄, lact_rmul, lact_mul, ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.rmul_assoc]
    have e₆ := eq_of_rmul_lact_eq (B.X (π k₂)) γ.2 (Subgroup.mul_mem _ γ'.2 hh) hx₁ hb
      (ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.mul_mem _ hb₃ hb') e₅
    rw [Subgroup.mem_subgroupOf]
    have e₇ : ((γ⁻¹ * γ' : (B.X (π k₂)).Γ) : GL (Fin r) E) = (MulAut.conj (δ k₂) g)⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, e₆]
      group
    rw [e₇]
    exact Subgroup.inv_mem _ (Subgroup.mem_map.2 ⟨g, hg, rfl⟩)
  · rintro ⟨y₂, hy⟩ ⟨y₂', hy'⟩ ⟨k₂, hk⟩ γ γ' ⟨x₂, t, x₁, b, hb, ht, hm, e⟩ ⟨x₂', t', x₁', b', hb', ht', hm', e'⟩ hγ
    subst hk
    rw [Subgroup.mem_subgroupOf] at hγ
    obtain ⟨g, hg, hgγ⟩ := Subgroup.mem_map.1 hγ
    have hc : (γ.1)⁻¹ * γ'.1 = MulAut.conj (δ k₂) g := by
      rw [← Subgroup.coe_inv, ← Subgroup.coe_mul]
      exact hgγ.symm
    have e₁ := eq_rmul_lact (B.X (π k₂)) hb (e.symm.trans e')
    rw [hc] at e₁
    obtain ⟨b₂, hb₂, e₂⟩ := (moved_iff (hΨ k₂ (π k₂)) (δ k₂) g hm' hm).2
      ⟨_, ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.mul_mem _ hb' (ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.invF_mem _ hb), e₁⟩
    obtain ⟨s, hs⟩ := (hC.2.2.2.1 k₂ k₂ x₂' x₂).2 ⟨g, hg, b₂, hb₂, by rw [e₂]⟩
    exact Subtype.ext (frOver_inj d hG hy hy' (ht.1.trans (hs.1.trans ht'.1.symm)))
  · rintro ⟨k₂, rfl⟩ ⟨γ, hγ⟩
    have hx₁ : lact γ⁻¹ x'.1 ∈ (B.X (π k₂)).dom :=
      (ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf.lact_mem_dom_iff _ (Subgroup.inv_mem _ hγ) _).2 x'.2
    obtain ⟨x₂, hm⟩ := exists_moved_back (hΨ k₂ (π k₂)) (δ k₂) (lact γ⁻¹ x'.1)
    have hx₂ : x₂ ∈ (C.X k₂).dom := mem_dom_of_moved (δ k₂) (hp k₂ _) (hΨ k₂ _) (hGm k₂) (hiso k₂) hm hx₁
    obtain ⟨hx₁', s, -, y₀, hb₀, ho⟩ := hOv k₂ x₂ hx₂ _ hm
    have ex : x'.1 = rmul (lact γ (lact γ⁻¹ x'.1)) (ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.oneF _) := by
      rw [ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.rmul_oneF, ← lact_mul, mul_inv_cancel, lact_one]
    obtain ⟨t₁, ht₁⟩ := (hB.2.2.2.1 _ _ ⟨_, hx₁'⟩ x').2
      ⟨γ, hγ, ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.oneF _, ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.oneF_mem _, by rw [← ex]⟩
    have hw := G.2.1 _ _ _ _ _ (G.2.2.1 _ _ _ hb₀) ht₁
    have e : ((C.un k₂ ⟨x₂, hx₂⟩).x ≫ d.r) = (B.un (π k₂) x').x := ho.1.trans hw.1.symm
    obtain ⟨y₂, hy₂x, hy₂⟩ := exists_frOver (S := CAt σ₂) d (fun _ => rfl) (B.un (π k₂) x') _ e (C.un k₂ ⟨x₂, hx₂⟩).x_over
    exact ⟨⟨y₂, hy₂⟩, ⟨x₂, hx₂⟩, _, _, ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.oneF _, ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.oneF_mem _,
      frBor_lift d hG ho hy₂ hy₂x hw, hm, ex⟩

end Core

theorem frLifts_equiv_cosets : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r) (d : DeltaDat Xo c 0) (U₂ : ∀ σ : d.c₂.F →+* ℂ, Unf d.Xo₂ d.c₂ σ D.R.r) (dict₂ : ∀ σ : d.c₂.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U₂ σ).X k).Ψ D.R.r), Laws D j Xo c U dict → Laws D j d.Xo₂ d.c₂ U₂ dict₂ → d.IsLev → ∀ σ₂, GoodEmb d.c₂ σ₂ → ∀ (π : (U₂ σ₂).Comp → (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).Comp) (δ : (U₂ σ₂).Comp → GL (Fin D.R.r) D.host.E), (∀ k₂, ((U₂ σ₂).X k₂).Gm = ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Gm ∧ (∀ v w, herm ((U₂ σ₂).X k₂).Gm (((δ k₂) : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) (((δ k₂) : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm ((U₂ σ₂).X k₂).Gm v w) ∧ ((U₂ σ₂).X k₂).Γ.map (MulAut.conj (δ k₂)).toMonoidHom ≤ ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Γ ∧ (((U₂ σ₂).X k₂).Γ.map (MulAut.conj (δ k₂)).toMonoidHom).relIndex ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Γ ≠ 0 ∧ GlobalTheory.LevModel.Over d σ₂ (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))) (U₂ σ₂) k₂ (π k₂) (δ k₂)) → ∀ k (x' : ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).dom), letI : Algebra c.F (CAt σ₂) := (σ₂.comp (d.eF : c.F →+* d.c₂.F)).toAlgebra; Nonempty ({y₂ : FrPt d.Xo₂ d.c₂ (CAt σ₂) // FrOver d y₂ ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).un k x')} ≃ Σ k₂ : {k₂ // π k₂ = k}, ↥((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Γ ⧸ (((U₂ σ₂).X k₂.1).Γ.map (MulAut.conj (δ k₂.1)).toMonoidHom).subgroupOf ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Γ) := by
  intro D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ hd σ₂ hσ₂ π δ hyp k x'
  exact lifts_equiv d σ₂ (U _) (U₂ σ₂) (hL.unf _ (good_comp d σ₂ hσ₂)) (hL₂.unf σ₂ hσ₂) π δ
    (fun k₂ => (hyp k₂).1) (fun k₂ => (hyp k₂).2.1) (fun k₂ => (hyp k₂).2.2.1) (fun k₂ => (hyp k₂).2.2.2.2) k x'

end GlobalTheory.LevModel
