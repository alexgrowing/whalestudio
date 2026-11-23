import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WchartCompLe
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat

noncomputable section

namespace GlobalTheory.QuotSec

variable {X : Scheme.{0}}

abbrev rs {U V : X.Opens} (h : V ≤ U) : Γ(X, U) →+* Γ(X, V) := (X.presheaf.map (homOfLE h).op).hom

theorem rs_rs {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (s : Γ(X, U)) :
    rs h' (rs h s) = rs (h'.trans h) s := by
  simp only [rs]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem coe_res {U V : X.Opens} (h : V ≤ U) (u : Γ(X, U)ˣ) :
    ((res h u : Γ(X, V)ˣ) : Γ(X, V)) = rs h (u : Γ(X, U)) := rfl

theorem rs_coe_inv {U V : X.Opens} (h : V ≤ U) (u : Γ(X, U)ˣ) :
    rs h ((u⁻¹ : Γ(X, U)ˣ) : Γ(X, U)) = (((res h u)⁻¹ : Γ(X, V)ˣ) : Γ(X, V)) := by
  rw [← map_inv]; rfl

theorem res_g_self (L : LB X) (hL : L.IsLB) (i : L.ι) {V : X.Opens} (h : V ≤ L.U i ⊓ L.U i) :
    res h (L.g i i) = 1 := by
  apply Units.ext
  rw [coe_res, ← rs_rs (le_inf le_rfl le_rfl : L.U i ≤ L.U i ⊓ L.U i) (h.trans inf_le_left), ← coe_res,
    hL.g_self]
  simp

def GenRel (P Q : LB X) (a : ∀ p₁ q, Γ(X, P.U p₁ ⊓ Q.U q)ˣ) : Prop :=
  ∀ p₁ q p₁' q', res (inf_le_left : (P.U p₁ ⊓ Q.U q) ⊓ (P.U p₁' ⊓ Q.U q') ≤ P.U p₁ ⊓ Q.U q) (a p₁ q) =
    res (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
        (P.U p₁ ⊓ Q.U q) ⊓ (P.U p₁' ⊓ Q.U q') ≤ P.U p₁ ⊓ P.U p₁') (P.g p₁ p₁') *
      (res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
        (P.U p₁ ⊓ Q.U q) ⊓ (P.U p₁' ⊓ Q.U q') ≤ Q.U q ⊓ Q.U q') (Q.g q q'))⁻¹ *
      res (inf_le_right : (P.U p₁ ⊓ Q.U q) ⊓ (P.U p₁' ⊓ Q.U q') ≤ P.U p₁' ⊓ Q.U q') (a p₁' q')

theorem genRel_of_isGen (P Q : LB X) (α : LB.Gen (LB.div P Q)) (hα : α.IsGen) :
    GenRel P Q (fun p₁ q => α.s (p₁, q)) :=
  fun p₁ q p₁' q' => hα (p₁, q) (p₁', q')

theorem quot_compat (P Q : LB X) (hQ : Q.IsLB) (a : ∀ p₁ q, Γ(X, P.U p₁ ⊓ Q.U q)ˣ) (ha : GenRel P Q a)
    (σ : LB.Sec P) (q : Q.ι) (p₁ p₁' : P.ι) :
    rs (inf_le_left : (P.U p₁ ⊓ Q.U q) ⊓ (P.U p₁' ⊓ Q.U q) ≤ P.U p₁ ⊓ Q.U q)
      ((((a p₁ q)⁻¹ : Γ(X, P.U p₁ ⊓ Q.U q)ˣ) : Γ(X, P.U p₁ ⊓ Q.U q)) *
        rs (inf_le_left : P.U p₁ ⊓ Q.U q ≤ P.U p₁) (σ.f p₁)) =
    rs (inf_le_right : (P.U p₁ ⊓ Q.U q) ⊓ (P.U p₁' ⊓ Q.U q) ≤ P.U p₁' ⊓ Q.U q)
      ((((a p₁' q)⁻¹ : Γ(X, P.U p₁' ⊓ Q.U q)ˣ) : Γ(X, P.U p₁' ⊓ Q.U q)) *
        rs (inf_le_left : P.U p₁' ⊓ Q.U q ≤ P.U p₁') (σ.f p₁')) := by
  have e := ha p₁ q p₁' q
  rw [res_g_self Q hQ q, inv_one, _root_.mul_one] at e
  have hσ := congrArg (rs (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
        (P.U p₁ ⊓ Q.U q) ⊓ (P.U p₁' ⊓ Q.U q) ≤ P.U p₁ ⊓ P.U p₁')) (σ.compat p₁ p₁')
  simp only [map_mul, rs_rs] at hσ ⊢
  rw [rs_coe_inv, rs_coe_inv, e, hσ, ← coe_res, mul_inv_rev, Units.val_mul, _root_.mul_assoc,
    Units.inv_mul_cancel_left]

theorem exists_quot_sec (P Q : LB X) (hP : P.IsLB) (hQ : Q.IsLB) (a : ∀ p₁ q, Γ(X, P.U p₁ ⊓ Q.U q)ˣ)
    (ha : GenRel P Q a) (σ : LB.Sec P) :
    ∃ s : LB.Sec Q, ∀ p₁ q, rs (inf_le_left : P.U p₁ ⊓ Q.U q ≤ P.U p₁) (σ.f p₁) =
      ((a p₁ q : Γ(X, P.U p₁ ⊓ Q.U q)ˣ) : Γ(X, P.U p₁ ⊓ Q.U q)) *
        rs (inf_le_right : P.U p₁ ⊓ Q.U q ≤ Q.U q) (s.f q) := by
  have hcov : ∀ (V : X.Opens), V ≤ ⨆ p₁, P.U p₁ ⊓ V := fun V x hx => by
    have : x ∈ (⨆ p₁, P.U p₁ : X.Opens) := by rw [hP.cover]; trivial
    obtain ⟨p₁, hp⟩ := TopologicalSpace.Opens.mem_iSup.1 this
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨p₁, hp, hx⟩
  have hglue : ∀ q, ∃ t : Γ(X, Q.U q), ∀ p₁, rs (inf_le_right : P.U p₁ ⊓ Q.U q ≤ Q.U q) t =
      (((a p₁ q)⁻¹ : Γ(X, P.U p₁ ⊓ Q.U q)ˣ) : Γ(X, P.U p₁ ⊓ Q.U q)) *
        rs (inf_le_left : P.U p₁ ⊓ Q.U q ≤ P.U p₁) (σ.f p₁) := fun q =>
    (X.sheaf.existsUnique_gluing' (fun p₁ => P.U p₁ ⊓ Q.U q) (Q.U q) (fun _ => homOfLE inf_le_right)
      (hcov (Q.U q)) _ (fun p₁ p₁' => quot_compat P Q hQ a ha σ q p₁ p₁')).exists
  choose t ht using hglue
  refine ⟨⟨t, fun q q' => ?_⟩, fun p₁ q => ?_⟩
  · refine X.sheaf.eq_of_locally_eq' (fun p₁ => P.U p₁ ⊓ (Q.U q ⊓ Q.U q')) (Q.U q ⊓ Q.U q')
      (fun _ => homOfLE inf_le_right) (hcov _) _ _ (fun p₁ => ?_)
    change rs _ (rs _ (t q)) = rs _ ((Q.g q q' : Γ(X, Q.U q ⊓ Q.U q')) * rs _ (t q'))
    simp only [map_mul, rs_rs]
    rw [      ← rs_rs (inf_le_right : P.U p₁ ⊓ Q.U q ≤ Q.U q)
        (le_inf inf_le_left (inf_le_right.trans inf_le_left) : P.U p₁ ⊓ (Q.U q ⊓ Q.U q') ≤ P.U p₁ ⊓ Q.U q),
      ← rs_rs (inf_le_right : P.U p₁ ⊓ Q.U q' ≤ Q.U q')
        (le_inf inf_le_left (inf_le_right.trans inf_le_right) : P.U p₁ ⊓ (Q.U q ⊓ Q.U q') ≤ P.U p₁ ⊓ Q.U q'),
      ht, ht]
    have e := congrArg (fun u : Γ(X, (P.U p₁ ⊓ Q.U q) ⊓ (P.U p₁ ⊓ Q.U q'))ˣ =>
      rs (le_inf (le_inf inf_le_left (inf_le_right.trans inf_le_left))
        (le_inf inf_le_left (inf_le_right.trans inf_le_right)) :
          P.U p₁ ⊓ (Q.U q ⊓ Q.U q') ≤ (P.U p₁ ⊓ Q.U q) ⊓ (P.U p₁ ⊓ Q.U q')) (u⁻¹ : Γ(X, _)ˣ)) (ha p₁ q p₁ q')
    rw [res_g_self P hP p₁, _root_.one_mul, mul_inv_rev, inv_inv] at e
    simp only [map_mul, rs_rs, rs_coe_inv, Units.val_mul, ← coe_res] at e ⊢
    simp only [map_inv, ReciprocityTheory.ChartRestriction.G.DVR.res_res'] at e ⊢
    rw [e]
    ring
  · rw [ht, ← _root_.mul_assoc, Units.mul_inv, _root_.one_mul]

end GlobalTheory.QuotSec

namespace GlobalTheory.HomFixMat

theorem divSec_exists : ∀ {X Z₁ Z₂ : Scheme.{0}} (L : LB Z₁) (M : LB Z₂) (f : X ⟶ Z₁) (g : X ⟶ Z₂) (a : ℤ) (α : LB.Gen (LB.div (powPull M g a) (powPull L f a))), α.IsGen → L.IsLB → M.IsLB → ∀ σ : LB.Sec (powPull M g a), ∃ s : LB.Sec (powPull L f a), ∀ p : (Fin 1 → M.ι) × (Fin 1 → L.ι), (X.presheaf.map (homOfLE (inf_le_left : LB.wchart M (fun _ : Fin 1 => g) p.1 ⊓ LB.wchart L (fun _ : Fin 1 => f) p.2 ≤ LB.wchart M (fun _ : Fin 1 => g) p.1)).op).hom (σ.f p.1) = (show Γ(X, LB.wchart M (fun _ : Fin 1 => g) p.1 ⊓ LB.wchart L (fun _ : Fin 1 => f) p.2) from (α.s p).val) * (X.presheaf.map (homOfLE (inf_le_right : LB.wchart M (fun _ : Fin 1 => g) p.1 ⊓ LB.wchart L (fun _ : Fin 1 => f) p.2 ≤ LB.wchart L (fun _ : Fin 1 => f) p.2)).op).hom (s.f p.2) := by
  intro X Z₁ Z₂ L M f g a α hα hL hM σ
  obtain ⟨s, hs⟩ := GlobalTheory.QuotSec.exists_quot_sec (powPull M g a) (powPull L f a)
    (ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB M hM _ _) (ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB L hL _ _)
    (fun p₁ q => α.s (p₁, q)) (GlobalTheory.QuotSec.genRel_of_isGen _ _ α hα) σ
  exact ⟨s, fun p => hs p.1 p.2⟩

end GlobalTheory.HomFixMat
