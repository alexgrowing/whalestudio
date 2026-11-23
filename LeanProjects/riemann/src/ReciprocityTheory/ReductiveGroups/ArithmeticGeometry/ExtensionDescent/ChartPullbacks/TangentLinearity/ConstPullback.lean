import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out.TLinPf

open Semi

theorem glue {Y : Scheme.{0}} {κ : Type} (U : κ → Y.Opens) (hc : ⨆ j, U j = ⊤)
    (f : ∀ j, Γ(Y, U j))
    (h : ∀ i j, (Y.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op).hom (f i) =
      (Y.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op).hom (f j)) :
    ∃ s : Γ(Y, ⊤), ∀ j, (Y.presheaf.map (homOfLE (le_top : U j ≤ ⊤)).op).hom s = f j := by
  obtain ⟨s, hs, -⟩ := Y.sheaf.existsUnique_gluing' U ⊤ (fun j => homOfLE le_top) hc.ge f h
  exact ⟨s, hs⟩

theorem eq_local {Y : Scheme.{0}} {κ : Type} (U : κ → Y.Opens) (hc : ⨆ j, U j = ⊤)
    (s t : Γ(Y, ⊤))
    (h : ∀ j, (Y.presheaf.map (homOfLE (le_top : U j ≤ ⊤)).op).hom s =
      (Y.presheaf.map (homOfLE (le_top : U j ≤ ⊤)).op).hom t) : s = t :=
  Y.sheaf.eq_of_locally_eq' U ⊤ (fun j => homOfLE le_top) hc.ge s t h

theorem ratio_glue {Y : Scheme.{0}} (L : LB Y) (hc : ⨆ j, L.U j = ⊤) (t t' : LB.Gen L)
    (ht : t.IsGen) (ht' : t'.IsGen) :
    ∃ ρ : Γ(Y, ⊤)ˣ, ∀ j, t.s j = res le_top ρ * t'.s j := by
  obtain ⟨s⟩ := t
  obtain ⟨s'⟩ := t'
  unfold LB.Gen.IsGen at ht ht'
  dsimp only at ht ht' ⊢
  have hcov : (⊤ : Y.Opens) ≤ ⨆ j, L.U j := hc.ge
  have key : ∀ (f : ∀ j, Γ(Y, L.U j)),
      (∀ i j, (Y.presheaf.map (homOfLE (inf_le_left : L.U i ⊓ L.U j ≤ L.U i)).op).hom (f i) =
        (Y.presheaf.map (homOfLE (inf_le_right : L.U i ⊓ L.U j ≤ L.U j)).op).hom (f j)) →
      ∃ r : Γ(Y, ⊤), ∀ j, (Y.presheaf.map (homOfLE (le_top : L.U j ≤ ⊤)).op).hom r = f j := by
    intro f hf
    obtain ⟨r, hr, -⟩ := TopCat.Sheaf.existsUnique_gluing' (F := Y.sheaf) (U := L.U) ⊤
      (fun j => homOfLE le_top) hcov f hf
    exact ⟨r, hr⟩
  have uniq : ∀ a b : Γ(Y, ⊤), (∀ j, (Y.presheaf.map (homOfLE (le_top : L.U j ≤ ⊤)).op).hom a =
      (Y.presheaf.map (homOfLE (le_top : L.U j ≤ ⊤)).op).hom b) → a = b := by
    intro a b h
    exact TopCat.Sheaf.eq_of_locally_eq' (F := Y.sheaf) (U := L.U) ⊤ (fun j => homOfLE le_top) hcov a b h
  have hu : ∀ i j, res (inf_le_left : L.U i ⊓ L.U j ≤ L.U i) (s i * (s' i)⁻¹) =
      res (inf_le_right : L.U i ⊓ L.U j ≤ L.U j) (s j * (s' j)⁻¹) := by
    intro i j
    rw [map_mul, map_inv, map_mul, map_inv, ht i j, ht' i j, _root_.mul_inv, _root_.mul_mul_mul_comm,
      _root_.mul_inv_cancel, _root_.one_mul]
  have hu' : ∀ i j, res (inf_le_left : L.U i ⊓ L.U j ≤ L.U i) (s i * (s' i)⁻¹)⁻¹ =
      res (inf_le_right : L.U i ⊓ L.U j ≤ L.U j) (s j * (s' j)⁻¹)⁻¹ := by
    intro i j
    rw [map_inv, map_inv, hu i j]
  obtain ⟨r, hr⟩ := key (fun j => ((s j * (s' j)⁻¹ : _ˣ) : Γ(Y, L.U j)))
    (fun i j => congrArg Units.val (hu i j))
  obtain ⟨r', hr'⟩ := key (fun j => (((s j * (s' j)⁻¹)⁻¹ : _ˣ) : Γ(Y, L.U j)))
    (fun i j => congrArg Units.val (hu' i j))
  have hrr : r * r' = 1 := by
    apply uniq
    intro j
    rw [map_mul, map_one, hr j, hr' j]
    exact Units.mul_inv _
  let ρ : Γ(Y, ⊤)ˣ := ⟨r, r', hrr, by rw [mul_comm]; exact hrr⟩
  refine ⟨ρ, fun j => ?_⟩
  have e : res (le_top : L.U j ≤ ⊤) ρ = s j * (s' j)⁻¹ := Units.ext (hr j)
  rw [e, inv_mul_cancel_right]

lemma exists_chart {X : Scheme.{0}} (L : LB X) (hL : L.IsLB) (y : X) : ∃ i, y ∈ L.U i := by
  have : y ∈ (⨆ i, L.U i : X.Opens) := by rw [hL.cover]; trivial
  simpa [TopologicalSpace.Opens.mem_iSup] using this

theorem idx_exists {X Y : Scheme.{0}} (L : LB X) (hL : L.IsLB) (y : Y) :
    ∃ idx : (Y ⟶ X) → L.ι, ∀ ψ, ψ.base y ∈ L.U (idx ψ) :=
  ⟨fun ψ => (exists_chart L hL (ψ.base y)).choose,
   fun ψ => (exists_chart L hL (ψ.base y)).choose_spec⟩

theorem linComb_cover {X Y : Scheme.{0}} (L : LB X) (hL : L.IsLB) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) : ⨆ j, (LB.LinComb L φ ε).U j = ⊤ := by
  refine eq_top_iff.2 fun y _ => ?_
  obtain ⟨idx, hidx⟩ := idx_exists L hL y
  exact TopologicalSpace.Opens.mem_iSup.2
    ⟨fun k => idx (φ k), Set.mem_iInter.2 fun k => hidx (φ k)⟩

theorem isAb_pullback {S S' : Scheme.{0}} (φ : S' ⟶ S) (A : Over S) [GrpObj A]
    (hA : IsAbelianScheme A) : IsAbelianScheme ((Over.pullback φ).obj A) := by
  have := hA.comm
  have := hA.smooth
  have := hA.proper
  have := hA.geomConnected
  exact
    { comm := Functor.isCommMonObj_obj
      smooth := by change Smooth (pullback.snd A.hom φ); infer_instance
      proper := by change IsProper (pullback.snd A.hom φ); infer_instance
      geomConnected := by change GeometricallyConnected (pullback.snd A.hom φ); infer_instance }

theorem const_pullback (hGF : GlobalFnsSt) {S S' : Scheme.{0}} (φ : S' ⟶ S) (A : Over S)
    [GrpObj A] (hA : IsAbelianScheme A) (v : Γ(((Over.pullback φ).obj A).left, ⊤)) :
    ∃ κ : Γ(S', ⊤), ((Over.pullback φ).obj A).hom.appTop.hom κ = v :=
  (hGF _ _ (isAb_pullback φ A hA)).2 v

end ReciprocityTheory.ChartRestriction.G.Out.TLinPf
