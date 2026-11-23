import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WithISelf
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsCoordPtFibre
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomTransport
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsThetaPtDown
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionMapsCompatibleInLevelStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel

namespace GlobalTheory.RelabelCoords

theorem isCoordPt_unit_mul {S : Scheme.{0}} {P : PolAV S} {k : ℕ} {T : Over S} {I : Type} {x : I → (T ⟶ P.A)}
    {z : T ⟶ P.A} {v w : I → Γ(T.left, ⊤)} (u : Γ(T.left, ⊤)ˣ) (h8 : ∀ i, v i = u.val * w i)
    (H : IsCoordPt P k x z w) : IsCoordPt P k x z v := by
  obtain ⟨ho, hu, th, s1, α, τ, U, s2, h1, h2, h3, h4, h5, h6, h7⟩ := H
  refine ⟨ho, hu, th, s1, α, ⟨fun j => τ.s j * InhTate.gv u⁻¹ _⟩, U, s2, h1, h2, fun i j => ?_, h4, h5, h6, fun i j => ?_⟩
  · rw [map_mul, map_mul, h3 i j, InhTate.res_gv, InhTate.res_gv, _root_.mul_assoc]
  · rw [h7 i j, h8 i, map_mul]
    have e : (T.left.presheaf.map (homOfLE (le_top : LB.wchart P.L (fun _ : Fin 1 => z.left) j ≤ ⊤)).op).hom u.val *
        (T.left.presheaf.map (homOfLE (le_top : LB.wchart P.L (fun _ : Fin 1 => z.left) j ≤ ⊤)).op).hom
          (u⁻¹).val = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    have key : ∀ {A : Type} [CommRing A] (a b c d : A), a * b = 1 → c * d = a * c * (d * b) := fun a b c d h => by
      linear_combination (-(c * d)) * h
    exact key _ _ _ _ e

theorem twRel_unique {O : Type} [CommRing O] {N : NumD O} {k : ℕ} {β : N.Form k} {u r : Oˣ} {j : ℕ} {q : N.QT j}
    {p p' : (N.twist β u).QT j} (h : TwRel β u r q p) (h' : TwRel β u r q p') : p = p' :=
  Subtype.ext (Prod.ext (h.1.trans h'.1.symm)
    (NumD.Gt.ext (h.2.1.trans h'.2.1.symm) (funext fun z => (h.2.2 z).trans (h'.2.2 z).symm)))

theorem series_iso {C : Type} [NormedField C] {N N' : NumD C} (J : NumD.Iso N N') {m : ℕ} (hm : Odd m)
    {p : N.QT (m ^ 2)} {p' : N'.QT (m ^ 2)} (h₁ : p'.1.1.toAdd = J.e p.1.1.toAdd) (h₂ : J.Rel p.1.2 p'.1.2) :
    N.tx m p = (J.lam⁻¹ : Cˣ) * N'.tx m p' ∧
      ∀ g g', J.Rel g g' → N.ev m p g = ((J.lam * J.h g.b ^ (m ^ 2))⁻¹ : Cˣ) * N'.ev m p' g' := by
  have H := (NumD.hom_transport C C (RingHom.id C) N N' (TateInh.homOfIso J)).2.2.2.2 m hm p p' h₁ h₂
  refine ⟨?_, fun g g' hg => ?_⟩
  · have e : N'.tx m p' = J.lam * N.tx m p := by
      rw [NumD.tx, NumD.tx, ← J.e.toEquiv.tsum_eq, ← tsum_mul_left]
      exact tsum_congr fun χ => (H χ).1
    rw [e, Units.inv_mul_cancel_left]
  · have e : N'.ev m p' g' = (J.lam * J.h g.b ^ (m ^ 2) : Cˣ) * N.ev m p g := by
      rw [NumD.ev, NumD.ev, ← J.e.toEquiv.tsum_eq, ← tsum_mul_left]
      exact tsum_congr fun χ => (H χ).2 g g' hg
    rw [e, Units.inv_mul_cancel_left]

theorem theta_coord : GlobalTheory.UT.LL → BrGtSt → TXSt → EVSt → AllD fun {E} _ _ _ {H} D => ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C] (o : Full D C) (M : Mdl o) (I : FullI o) (N N' : NumD C) (ν' : NumOf M.P.D.toPre C N') (k : ℕ) (β : N.Form k) (u : Cˣ) (r : ℕ → Cˣ) (J : NumD.Iso (N.twist β u) N') (q : ∀ j : ℕ, D.La → N.QT j), (∀ j, 0 < j → ∀ x, ∃ (q' : N'.QT j) (p' : QkPt M.P.D.toPre C j) (z : TFK (R := M.W) C ⟶ M.P.A.A), TwJ β u (r j) J (q j x) q' ∧ ν'.QPt p' q' ∧ z.left = (I.ev j x).left ≫ M.φ ∧ M.P.ToA C j p' z) → ∀ m, Odd m → ∀ p : D.La → (N.twist β u).QT (m ^ 2), (∀ x, TwRel β u (r (m ^ 2)) (q _ x) (p x)) → (withI o I).Theta m (fun x => (N.twist β u).tx m (p x)) ∧ ∀ j, 0 < j → ∀ z (p₀ : (N.twist β u).QT j), TwRel β u (r j) (q j z) p₀ → (withI o I).Coord m (I.ev j z) fun x => (N.twist β u).ev m (p x) p₀.1.2 := by
  intro hL hB hT hE E _ _ _ H D C _ _ _ _ _ o M I N N' ν' k β u r J q hq m hm p hp
  have hm2 : 0 < m ^ 2 := pow_pos hm.pos 2
  choose q' p' x htw hqp hx hA using hq (m ^ 2) hm2
  have hJ : ∀ a, (q' a).1.1.toAdd = J.e (p a).1.1.toAdd ∧ J.Rel (p a).1.2 (q' a).1.2 := fun a => by
    obtain ⟨p₁, h₁, h₂⟩ := htw a
    rwa [twRel_unique h₁ (hp a)] at h₂
  let τ : (baseOver (Sp C)).left ⟶ (TFK (R := M.W) C).left := 𝟙 (Sp C)
  have : IsIso τ := inferInstanceAs (IsIso (𝟙 (Sp C)))
  have hτ : τ ≫ (TFK (R := M.W) C).hom = (baseOver (Sp C)).hom ≫ jFK (R := M.W) C := rfl
  have hx' : ∀ a, τ ≫ (x a).left = (I.ev (m ^ 2) a).left ≫ M.φ := fun a => (Category.id_comp _).trans (hx a)
  have hk : ∀ a, I.ev (m ^ 2) a ^ (m ^ 2) = 1 := fun a => (I.onto _ hm2 _).2 ⟨a, rfl⟩
  have hs : Subsingleton (Sp C) := inferInstanceAs (Subsingleton (PrimeSpectrum C))
  have hn : Nonempty (Sp C) := inferInstanceAs (Nonempty (PrimeSpectrum C))
  have hτv : ∀ (c : Cˣ) (a : C), fnOf (c * a) = (unitOn c).val * (show Γ(Sp C, ⊤) from τ.appTop.hom (fnOf a)) := fun c a =>
    map_mul (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom _ _
  refine ⟨?_, fun j hj z p₀ h₀ => ?_⟩
  · have Q := hT M.W _ M.cdv rfl M.P.D M.P.A M.t.G M.t.semi M.P.U C M.ext N' ν' m hm D.La p' q' x hA hqp
    have : Subsingleton (TFK (R := M.W) C).left := hs
    have : Nonempty (TFK (R := M.W) C).left := hn
    have : Subsingleton (baseOver (Sp C)).left := hs
    have Q₁ := ThetaPtUp.isThetaPtOver_down τ M.cart M.lb hτ hx' hk (ThetaCoord.isThetaPtOver_of_subsingleton _ Q)
    have Q₂ := (isCoordPt_one_iff o.P m (T := baseOver (Sp C)) _ _).2 ⟨hm, Q.2.1, Q₁⟩
    have Q₃ := isCoordPt_unit_mul (v := fun a => fnOf ((N.twist β u).tx m (p a))) (unitOn J.lam⁻¹)
      (fun a => by rw [(series_iso J hm (hJ a).1 (hJ a).2).1]; exact hτv _ _) Q₂
    exact ThetaNest.isThetaPt_of_over _ hm Q.2.1 ((isCoordPt_one_iff _ _ _ _).1 Q₃).2.2
  · obtain ⟨q₁, p₁, y, ⟨p₂, t₁, -, t₂⟩, hq₁, hy, hA₁⟩ := hq j hj z
    obtain rfl := twRel_unique h₀ t₁
    let q₄ : N'.QT (j * 4) := ⟨(q₁.1.1 ^ 4, q₁.1.2), by
      rw [NumD.mem_QT, pow_mul, N'.mem_QT.1 q₁.2, toAdd_pow, NumD.io_nsmul]⟩
    have B := hB M.W M.P.D.toPre M.P.D.psi_even M.P.D.tau_bimult C N' ν'
    obtain ⟨p₄, hp₄⟩ := (B.2.2.2.2 (j * 4)).2.1 q₄
    have e₁ : p₄.y = 4 • p₁.y := by
      rw [← hp₄.1, ← hq₁.1, ← map_nsmul]; rfl
    have e₂ : p₄.g = p₁.g := (B.2.1 q₁.1.2).unique hp₄.2 hq₁.2
    have := M.admissible_base_of_complete_dvr.2
    have hA₄ := ((GlobalTheory.T.uniformisation_torsion_maps_compatible_in_level hL M.W _ M.admissible_base_of_complete_dvr.1 M.P.D M.P.A M.t.G M.t.semi M.P.U C j 4 (j * 4) hj (by norm_num) rfl
      p₁ p₄ y).1 e₁ e₂).1 hA₁
    have Q := hE M.W _ M.cdv rfl M.P.D M.P.A M.t.G M.t.semi M.P.U C M.ext N' ν' m hm D.La p' q' x hA hqp
      (j * 4) (by omega) p₄ q₄ y hA₄ hp₄
    have Q₁ := FullExtend.isCoordPt_move τ M.cart M.lb τ (𝟙 _) (Category.comp_id _) hτ (fun th h s => by
      obtain ⟨c, hc⟩ := h s
      have e := VVRank.pullM_id M.P.A.A M.P.A.isLB 1 (SecM.ofSec M.P.A.A th)
      exact ⟨c, fun j => (hc j).trans (congrArg (_ * ·) (congrArg (fun q => q.1 j) e).symm)⟩)
      hx' hk (z := I.ev j z) ((Category.id_comp _).trans hy) Q
    exact isCoordPt_unit_mul (v := fun a => fnOf ((N.twist β u).ev m (p a) p₀.1.2))
      (unitOn (J.lam * J.h p₀.1.2.b ^ (m ^ 2))⁻¹)
      (fun a => by rw [(series_iso J hm (hJ a).1 (hJ a).2).2 _ _ t₂]; exact hτv _ _) Q₁

end GlobalTheory.RelabelCoords
