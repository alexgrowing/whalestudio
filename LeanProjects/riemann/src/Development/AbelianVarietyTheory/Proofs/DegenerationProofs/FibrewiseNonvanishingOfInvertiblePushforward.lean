import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

namespace GlobalTheory.ThetaLocal

open GlobalTheory.LB

variable {X Y : Scheme.{0}}

theorem mem_basicOpen_resG {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)) (x : X) :
    x ∈ X.basicOpen (resG X h a) ↔ x ∈ V ∧ x ∈ X.basicOpen a := by
  have : X.basicOpen (resG X h a) = V ⊓ X.basicOpen a := X.basicOpen_res a (homOfLE h).op
  rw [this]; rfl

theorem mem_basicOpen_appLE (f : Y ⟶ X) {U : X.Opens} {V : Y.Opens} (h : V ≤ f ⁻¹ᵁ U)
    (a : Γ(X, U)) (y : Y) :
    y ∈ Y.basicOpen ((f.appLE U V h).hom a) ↔ y ∈ V ∧ f y ∈ X.basicOpen a := by
  have : Y.basicOpen ((f.appLE U V h).hom a) = V ⊓ f ⁻¹ᵁ X.basicOpen a :=
    Scheme.basicOpen_appLE f V U h a
  rw [this]; rfl

theorem mem_basicOpen_mul {U : X.Opens} (a b : Γ(X, U)) (x : X) :
    x ∈ X.basicOpen (a * b) ↔ x ∈ X.basicOpen a ∧ x ∈ X.basicOpen b := by
  rw [Scheme.basicOpen_mul]; rfl

theorem nonvanishing_of_iso {L M : LB X} (hL : L.IsLB) (hM : M.IsLB) (w : LB.Iso L M) (hw : w.IsGen)
    {V : X.Opens} (s : Γ(toMod L, V)) (x : X) (p : M.ι)
    (hp : x ∈ X.basicOpen (coord ((isoOfGen hL hM w hw).hom.app V s) p)) :
    ∃ q, x ∈ X.basicOpen (coord s q) := by
  have hp' := X.basicOpen_le _ hp
  obtain ⟨q, hq⟩ := exists_chart hL x
  have e := coord_isoOfGen_hom_app hL hM w hw s p q (W := (V ⊓ M.U p) ⊓ (V ⊓ L.U q))
    inf_le_left inf_le_right (inf_le_inf inf_le_right inf_le_right)
  have e' := congrArg (fun a => x ∈ X.basicOpen a) e
  simp only [mem_basicOpen_mul, mem_basicOpen_resG, eq_iff_iff] at e'
  have hx : x ∈ (V ⊓ M.U p) ⊓ (V ⊓ L.U q) := ⟨hp', hp'.1, hq⟩
  exact ⟨q, (e'.1 ⟨hx, hp⟩).2.2⟩

theorem exists_sec_pull {L : LB X} {L' : LB Y} (hL : L.IsLB) (hL' : L'.IsLB) (F : Y ⟶ X) (w : LB.Iso L' (L.pull F))
    (hw : w.IsGen) {O : X.Opens} (hO : ⊤ ≤ F ⁻¹ᵁ O) (θ : ∀ i, Γ(X, O ⊓ L.U i)) (hθ : θ ∈ secOn L O) :
    ∃ θ' : L'.Sec, ∀ (y : Y) (i : L.ι), F y ∈ X.basicOpen (θ i) → ∃ k, y ∈ Y.basicOpen (θ'.f k) := by
  have hP : (L.pull F).IsLB := Semi.LB.isLB_pull hL F
  let e := isoOfGen hL' hP w hw
  let s : Γ(toMod (L.pull F), F ⁻¹ᵁ O) := pullSec L F O (mkSec θ hθ)
  let s' : Γ(toMod L', F ⁻¹ᵁ O) := e.inv.app _ s
  have hs : e.hom.app _ s' = s := by
    have := congrArg (fun q => q.app (F ⁻¹ᵁ O) s) e.inv_hom_id
    exact this
  refine ⟨globalEquiv L' ((toMod L').presheaf.map (homOfLE hO).op s'), fun y i hy => ?_⟩
  obtain ⟨k, hk⟩ := nonvanishing_of_iso hL' hP w hw s' y (fun _ => i) (by
    change y ∈ Y.basicOpen (coord (e.hom.app _ s') _)
    rw [hs]
    exact (mem_basicOpen_appLE F (pull_inf_le F O (fun _ => i)) (θ i) y).2
      ⟨⟨(X.basicOpen_le _ hy).1, mem_pull.2 (X.basicOpen_le _ hy).2⟩, hy⟩)
  refine ⟨k, ?_⟩
  rw [globalEquiv_f, coord_map, mem_basicOpen_resG, mem_basicOpen_resG]
  have := (Y.basicOpen_le _ hk).2
  exact ⟨this, ⟨trivial, this⟩, hk⟩

theorem thetaNZ_of_pushInvertible : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t₀ : SAB H S), PushInvertible t₀.G t₀.PP.L → ∀ (R : Type) [CommRing R] [IsLocalRing R] (ξ : Sp R ⟶ S) (t : SAB H (Sp R)) (_ : SABMap t t₀ ξ), ThetaNZ t.G t.PP.L := by
  intro E _ _ _ H S t₀ h R _ _ ξ t m
  obtain ⟨V, hV, θ, hθ, -, h2⟩ := h (ξ (IsLocalRing.closedPoint R))
  have hall : ∀ y : Sp R, ξ y ∈ V := fun y =>
    ((IsLocalRing.specializes_closedPoint y).map ξ.continuous).mem_open V.isOpen hV
  have hc : IsPullback m.cm.F t.G.hom t₀.G.hom ξ := m.cart.1
  have hpt : ∀ g : t.G.left, t₀.G.hom (m.cm.F g) = ξ (t.G.hom g) := fun g =>
    congrArg (fun q => q g) hc.w
  obtain ⟨w, hw, -⟩ := m.lin
  obtain ⟨θ', h'⟩ := exists_sec_pull t₀.PP.isLB t.PP.isLB m.cm.F w hw (O := t₀.G.hom ⁻¹ᵁ V)
    (fun g _ => by
      change t₀.G.hom (m.cm.F g) ∈ V
      rw [hpt]; exact hall _) θ hθ
  refine ⟨θ', fun y => ?_⟩
  obtain ⟨g, i, hg, hi⟩ := h2 (ξ y) (hall y)
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.exists_preimage_of_isPullback hc g y hg
  obtain ⟨k, hk⟩ := h' z i (by rw [hz₁]; exact hi)
  exact ⟨z, k, hz₂, hk⟩

end GlobalTheory.ThetaLocal
