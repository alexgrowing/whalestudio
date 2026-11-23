import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusMemOfSepAtBTate
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullUUnitsCompatGeneric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomDescent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LbIsoOfLbIsoFieldExt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon.BaseDescent

theorem exists_descent {K : Type} [Field K] (k₀ : Subfield K) [IsAlgClosed k₀] {S : Scheme.{0}} (g : Sp k₀ ⟶ S)
    (B₀ : Over (Sp k₀)) [GrpObj B₀] (B₁ : Over S) [GrpObj B₁] (B' : Over (Sp K)) [GrpObj B']
    (h₀ : IsAbelianScheme B₀) (h₁ : IsAbelianScheme B₁) {π₀ : B'.left ⟶ B₀.left} {δ : B'.left ⟶ B₁.left}
    (p₀ : IsGrpPullback B' B₀ (spMap k₀.subtype) π₀) (p₁ : IsGrpPullback B' B₁ (spMap k₀.subtype ≫ g) δ) :
    ∃ κ₀ : B₀.left ⟶ B₁.left, π₀ ≫ κ₀ = δ := by
  let i : Sp K ⟶ Sp k₀ := spMap k₀.subtype
  let B₂ := (Over.pullback g).obj B₁
  obtain ⟨e₁, m₁, he₁⟩ := grpPullback_iso (isGrpPullback_pullback B₀ i) p₀
  obtain ⟨e₂, m₂, he₂⟩ := grpPullback_iso p₁ ((isGrpPullback_pullback B₂ i).comp (isGrpPullback_pullback B₁ g))
  obtain ⟨f₀, ⟨-, hf⟩, -⟩ := GlobalTheory.AlgClosedDescent.hom_descent k₀ K B₀ B₂ h₀ (TLinPf.isAb_pullback g B₁ h₁)
    (e₁.hom ≫ e₂.hom) (by exact inferInstanceAs (IsMonHom (e₁.hom ≫ e₂.hom)))
  refine ⟨f₀.left ≫ pullback.fst B₁.hom g, ?_⟩
  have hi : IsIso e₁.hom.left := ⟨⟨e₁.inv.left, by rw [← Over.comp_left, e₁.hom_inv_id, Over.id_left],
    by rw [← Over.comp_left, e₁.inv_hom_id, Over.id_left]⟩⟩
  have h2 : (e₁.hom ≫ e₂.hom).left ≫ pullback.fst B₂.hom i = pullback.fst B₀.hom i ≫ f₀.left := by
    exact (congrArg (fun q => q.left ≫ pullback.fst B₂.hom i) hf).symm.trans (pullback.lift_fst _ _ _)
  rw [← cancel_epi e₁.hom.left, ← he₂, ← Category.assoc, he₁, ← Category.assoc, ← h2]
  simp only [Over.comp_left, Category.assoc]

theorem lbIso_pull {X Y : Scheme.{0}} {P Q : LB X} (h : LBIso P Q) (f : Y ⟶ X) : LBIso (P.pull f) (Q.pull f) :=
  h.chartPull (Geo.Tor.chartPullPull P f f rfl) (Geo.Tor.chartPullPull Q f f rfl)

theorem exists_lbIso {K : Type} [Field K] (k₀ : Subfield K) (B₀ : Over (Sp k₀)) [GrpObj B₀] (B' : Over (Sp K)) [GrpObj B']
    (h₀ : IsAbelianScheme B₀) {A B₁ : Scheme.{0}} {π₀ : B'.left ⟶ B₀.left} {π₁ : B'.left ⟶ A} {β : A ⟶ B₁}
    {κ₀ : B₀.left ⟶ B₁} (p₀ : IsGrpPullback B' B₀ (spMap k₀.subtype) π₀) (hκ₀ : π₀ ≫ κ₀ = π₁ ≫ β)
    {L : LB A} {M₀ : LB B₀.left} {M₁ : LB B₁} (hL : L.IsLB) (hM₀ : M₀.IsLB) (hM₁ : M₁.IsLB)
    (w : LBIso (L.pull π₁) (M₀.pull π₀)) (w' : LBIso L (M₁.pull β)) : LBIso M₀ (M₁.pull κ₀) := by
  obtain ⟨e, -, he⟩ := grpPullback_iso (isGrpPullback_pullback B₀ (spMap k₀.subtype)) p₀
  have P : ∀ {X Y : Scheme.{0}} {N : LB X}, N.IsLB → ∀ f : Y ⟶ X, (N.pull f).IsLB := fun h f => pull_isLB h f
  have a₁ : LBIso (M₀.pull π₀) ((M₁.pull β).pull π₁) :=
    LBIso.trans (P hM₀ _) (P hL _) (P (P hM₁ _) _) w.symm (lbIso_pull w' π₁)
  have a₂ : LBIso ((M₁.pull β).pull π₁) ((M₁.pull κ₀).pull π₀) :=
    LBIso.trans (P (P hM₁ _) _) (P hM₁ (π₁ ≫ β)) (P (P hM₁ _) _) (SepBModel.lbIso_two hM₁ β π₁).symm
      (hκ₀ ▸ SepBModel.lbIso_two hM₁ κ₀ π₀)
  have a₃ := lbIso_pull (LBIso.trans (P hM₀ _) (P (P hM₁ _) _) (P (P hM₁ _) _) a₁ a₂) e.hom.left
  refine lbIso_of_lbIso_fieldExt k₀ K k₀.subtype B₀ h₀ _ _ hM₀ (P hM₁ _) ?_
  have a₄ := LBIso.trans (P hM₀ _) (P (P hM₀ _) _) (P (P (P hM₁ _) _) _) (SepBModel.lbIso_two hM₀ π₀ e.hom.left) a₃
  have a₅ := LBIso.trans (P hM₀ _) (P (P (P hM₁ _) _) _) (P (P hM₁ _) _) a₄
    (SepBModel.lbIso_two (P hM₁ κ₀) π₀ e.hom.left).symm
  rw [he] at a₅
  exact a₅

theorem exists_unit {B' B₀ A B₁ : Scheme.{0}} {π₀ : B' ⟶ B₀} {π₁ : B' ⟶ A} {β : A ⟶ B₁} {κ₀ : B₀ ⟶ B₁}
    (hκ₀ : π₀ ≫ κ₀ = π₁ ≫ β) {L : LB A} {M₀ : LB B₀} {M₁ : LB B₁} (hL : L.IsLB) (hM₀ : M₀.IsLB) (hM₁ : M₁.IsLB)
    {w : LB.Iso (L.pull π₁) (M₀.pull π₀)} {w' : LB.Iso L (M₁.pull β)} {v : LB.Iso M₀ (M₁.pull κ₀)}
    (hw : w.IsGen) (hw' : w'.IsGen) (hv : v.IsGen) :
    ∃ ρ : Γ(B', ⊤)ˣ, ∀ (Z : Scheme.{0}) (f : Z ⟶ B') (z : Z) (j : L.ι) (m₀ : M₀.ι) (m₁ : M₁.ι),
      π₁ (f z) ∈ L.U j → π₀ (f z) ∈ M₀.U m₀ → β (π₁ (f z)) ∈ M₁.U m₁ →
      gw w' (f ≫ π₁) z m₁ j = gm f z ⊤ ρ * gw v (f ≫ π₀) z m₁ m₀ * gw w f z m₀ (fun _ => j) := by
  have hp : ∀ x : B', κ₀ (π₀ x) = β (π₁ x) := fun x => congrArg (fun q : B' ⟶ B₁ => q x) hκ₀
  let W : L.ι × M₀.ι × M₁.ι → B'.Opens := fun p =>
    π₁ ⁻¹ᵁ ((M₁.pull β).U (fun _ => p.2.2) ⊓ L.U p.1) ⊓ π₀ ⁻¹ᵁ ((M₁.pull κ₀).U (fun _ => p.2.2) ⊓ M₀.U p.2.1) ⊓
      ((M₀.pull π₀).U (fun _ => p.2.1) ⊓ (L.pull π₁).U (fun _ => p.1))
  let u : ∀ p, Γ(B', W p)ˣ := fun p =>
    res (inf_le_left.trans inf_le_left) (pullU π₁ _ (w'.s (fun _ => p.2.2, p.1))) *
      (res (inf_le_left.trans inf_le_right) (pullU π₀ _ (v.s (fun _ => p.2.2, p.2.1))))⁻¹ *
      (res inf_le_right (w.s (fun _ => p.2.1, fun _ => p.1)))⁻¹
  have hW : ∀ (x : B') p, x ∈ W p ↔ π₁ x ∈ L.U p.1 ∧ π₀ x ∈ M₀.U p.2.1 ∧ β (π₁ x) ∈ M₁.U p.2.2 := fun x p =>
    ⟨fun h => ⟨h.1.1.2, h.1.2.2, mem_pull.1 h.1.1.1⟩, fun h => ⟨⟨⟨mem_pull.2 h.2.2, h.1⟩,
      ⟨mem_pull.2 (by rw [hp]; exact h.2.2), h.2.1⟩⟩, mem_pull.2 h.2.1, mem_pull.2 h.1⟩⟩
  have hu : ∀ (Z : Scheme.{0}) (f : Z ⟶ B') (z : Z) p, f z ∈ W p → gm f z (W p) (u p) =
      gw w' (f ≫ π₁) z p.2.2 p.1 * (gw v (f ≫ π₀) z p.2.2 p.2.1)⁻¹ * (gw w f z p.2.1 (fun _ => p.1))⁻¹ := by
    intro Z f z p h
    refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ ?_)) ?_)
    · exact (gm_res f z _ h _).trans (gm_pull f π₁ z _ h.1.1 _)
    · exact (map_inv _ _).trans (congrArg (·⁻¹) ((gm_res f z _ h _).trans (gm_pull f π₀ z _ h.1.2 _)))
    · exact (map_inv _ _).trans (congrArg (·⁻¹) (gm_res f z _ h _))
  obtain ⟨ρ, hρ⟩ := glue_unit ⊤ W (fun _ => le_top) (fun x _ => by
      obtain ⟨j, hj⟩ := exists_chart hL (π₁ x)
      obtain ⟨m₀, h₀⟩ := exists_chart hM₀ (π₀ x)
      obtain ⟨m₁, h₁⟩ := exists_chart hM₁ (β (π₁ x))
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨(j, m₀, m₁), (hW x _).2 ⟨hj, h₀, h₁⟩⟩) u (fun p q x hx => by
      obtain ⟨a₁, a₂, a₃⟩ := (hW x p).1 hx.1
      obtain ⟨b₁, b₂, b₃⟩ := (hW x q).1 hx.2
      rw [hu _ _ x p hx.1, hu _ _ x q hx.2,
        (isGen_iff w').1 hw' _ (𝟙 B' ≫ π₁) x p.2.2 q.2.2 p.1 q.1 a₃ b₃ a₁ b₁,
        (isGen_iff v).1 hv _ (𝟙 B' ≫ π₀) x p.2.2 q.2.2 p.2.1 q.2.1 ((hp x).symm ▸ a₃) ((hp x).symm ▸ b₃) a₂ b₂,
        (isGen_iff w).1 hw _ (𝟙 B') x p.2.1 q.2.1 (fun _ => p.1) (fun _ => q.1) a₂ b₂ (mem_pull.2 a₁) (mem_pull.2 b₁),
        gm_pull_g L π₁ (𝟙 B') x (fun _ => p.1) (fun _ => q.1) (mem_pull.2 a₁) (mem_pull.2 b₁)]
      simp only [Category.assoc, hκ₀]
      simp only [mul_inv, inv_inv]
      generalize gm (𝟙 B' ≫ π₁ ≫ β) x _ _ = s
      generalize gm (𝟙 B' ≫ π₁) x _ _ = t
      generalize gm (𝟙 B' ≫ π₀) x _ _ = r
      rw [show ∀ a b c, s * t⁻¹ * a * (s⁻¹ * r * b) * (r⁻¹ * t * c) = (s * s⁻¹) * (t * t⁻¹) * (r * r⁻¹) * (a * b * c) from
        fun a b c => by ac_rfl]
      simp)
  refine ⟨ρ, fun Z f z j m₀ m₁ h₁ h₂ h₃ => ?_⟩
  have hm : f z ∈ W (j, m₀, m₁) := (hW _ _).2 ⟨h₁, h₂, h₃⟩
  rw [← gm_res f z le_top hm ρ, hρ, hu Z f z _ hm]
  rw [mul_right_comm _ _ (gw v _ _ _ _), inv_mul_cancel_right, inv_mul_cancel_right]

theorem gm_const {S S₀ : Scheme.{0}} (i : S ⟶ S₀) (B₀ : Over S₀) [GrpObj B₀] (B' : Over S) [GrpObj B']
    (h₀ : IsAbelianScheme B₀) {π₀ : B'.left ⟶ B₀.left} (p₀ : IsGrpPullback B' B₀ i π₀) (ρ : Γ(B'.left, ⊤)ˣ) (z : S)
    (c c' : S ⟶ B'.left) (hc : c ≫ B'.hom = 𝟙 _) (hc' : c' ≫ B'.hom = 𝟙 _) : gm c z ⊤ ρ = gm c' z ⊤ ρ := by
  obtain ⟨e, -, -⟩ := grpPullback_iso (isGrpPullback_pullback B₀ i) p₀
  obtain ⟨κ, hκ⟩ := TLinPf.const_pullback GlobalTheory.globalFns_holds i B₀ h₀ (e.hom.left.appTop.hom ρ.val)
  have hρ : ρ.val = B'.hom.appTop.hom κ := by
    have h1 : e.inv.left.appTop.hom (e.hom.left.appTop.hom ρ.val) = ρ.val := by
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, ← Over.comp_left, e.inv_hom_id]
      simp
    rw [← h1, ← hκ, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, Over.w]
  have key : ∀ d : S ⟶ B'.left, d ≫ B'.hom = 𝟙 _ → d.appTop.hom ρ.val = κ := fun d hd => by
    rw [hρ, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hd]
    simp
  apply Units.ext
  rw [gm_val c z ⊤ trivial, gm_val c' z ⊤ trivial]
  exact (congrArg (S.presheaf.germ ⊤ z trivial).hom ((key c hc).trans (key c' hc').symm))

private theorem inv_mul_cancel_left' {G : Type} [Group G] (a s b : G) : a * s⁻¹ * (s * b) = a * b := by group

theorem exists_const {K : Type} [Field K] (k₀ : Subfield K) {B₀ B₁ : Scheme.{0}} {M₀ : LB B₀} {M₁ : LB B₁} (hM₀ : M₀.IsLB)
    (hM₁ : M₁.IsLB) {κ₀ : B₀ ⟶ B₁} {v : LB.Iso M₀ (M₁.pull κ₀)} (hv : v.IsGen) (p : Fin 4 → (Sp k₀ ⟶ B₀))
    (τ₁ : LB.Gen (LB.LinComb M₀ p ![-1, 1, 1, -1])) (hτ : τ₁.IsGen) (z : Sp K) (m : Fin 4 → M₁.ι)
    (hm : ∀ k, κ₀ (p k (spMap k₀.subtype z)) ∈ M₁.U (m k)) (t : ((Sp K).presheaf.stalk z)ˣ)
    (ht : t ∈ (gm (spMap k₀.subtype) z ⊤).range) :
    ∃ x : k₀ˣ, ∀ J₀, Good M₀ z J₀ →
      gw v (spMap k₀.subtype ≫ p 0) z (m 0) (J₀ (spMap k₀.subtype ≫ p 0)) *
        (gw v (spMap k₀.subtype ≫ p 1) z (m 1) (J₀ (spMap k₀.subtype ≫ p 1)))⁻¹ *
        (gw v (spMap k₀.subtype ≫ p 2) z (m 2) (J₀ (spMap k₀.subtype ≫ p 2)))⁻¹ *
        gw v (spMap k₀.subtype ≫ p 3) z (m 3) (J₀ (spMap k₀.subtype ≫ p 3)) * t =
      gm (𝟙 (Sp K)) z ⊤ (unitOn (Units.map k₀.subtype.toMonoidHom x)) * val τ₁ (spMap k₀.subtype) z J₀ := by
  have : Subsingleton (Sp k₀) := inferInstanceAs (Subsingleton (PrimeSpectrum k₀))
  set i : Sp K ⟶ Sp k₀ := spMap k₀.subtype with hi
  have rg : ∀ (U : (Sp k₀).Opens) (a : Γ(Sp k₀, U)ˣ), i z ∈ U → gm i z U a ∈ (gm i z ⊤).range := fun U a h => by
    obtain ⟨x, hx⟩ := SepBModel.gm_field i z U h a
    exact ⟨_, hx.symm⟩
  choose I hI using fun χ : Sp K ⟶ B₀ => exists_chart hM₀ (χ z)
  have rw' : ∀ k, gw v (i ≫ p k) z (m k) (I (i ≫ p k)) ∈ (gm i z ⊤).range := fun k => by
    have h : p k (i z) ∈ (M₁.pull κ₀).U (fun _ => m k) ⊓ M₀.U (I (i ≫ p k)) := ⟨mem_pull.2 (hm k), hI (i ≫ p k)⟩
    obtain ⟨c, hc⟩ := rg _ (pullU (p k) _ (v.s (fun _ => m k, I (i ≫ p k)))) h
    exact ⟨c, hc.trans (gm_pull i (p k) z _ h _)⟩
  have rv : val τ₁ i z I ∈ (gm i z ⊤).range := rg _ _ (Good.mem hI p i)
  obtain ⟨c, hc⟩ := mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (rw' 0) (inv_mem (rw' 1))) (inv_mem (rw' 2))) (rw' 3)) ht)
    (inv_mem rv)
  obtain ⟨x, hx⟩ := SepBModel.gm_field i z ⊤ trivial c
  refine ⟨x, fun J₀ hJ₀ => ?_⟩
  have ch : ∀ k, gw v (i ≫ p k) z (m k) (J₀ (i ≫ p k)) =
      (gm (i ≫ p k) z _ (M₀.g (J₀ (i ≫ p k)) (I (i ≫ p k))))⁻¹ * gw v (i ≫ p k) z (m k) (I (i ≫ p k)) := fun k => by
    rw [(isGen_iff v).1 hv _ (i ≫ p k) z (m k) (m k) _ _ (hm k) (hm k) (hJ₀ _) (hI _),
      gm_self hM₁ ((i ≫ p k) ≫ κ₀) z (hm k), _root_.one_mul]
  have cv : val τ₁ i z J₀ = _ * val τ₁ i z I := gen_trans hτ i z (hJ₀.mem p i) (Good.mem hI p i)
  rw [← SepBModel.gm_spMap, ← hx, hc, ch, ch, ch, ch, cv]
  simp only [trF, Fin.prod_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, zpow_neg, zpow_one,
    mul_inv, inv_inv]
  generalize val τ₁ i z I = s
  rw [mul_comm _ s, inv_mul_cancel_left' _ s]
  ac_rfl

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R]
    (Q : DegPre R) (τ₀ : Gens Q) (K : Type) [Field K] [IsAlgClosed K] (ev : R →+* K) (k₀ : Subfield K), IsAlgClosed k₀ →
    ∀ (W₀ : Type) [CommRing W₀] (ιb : W₀ →+* R), FromBase Q τ₀ ιb → (∀ a, ev (ιb a) ∈ k₀) →
    ∀ (B₀ : Over (Sp k₀)) [GrpObj B₀] [IsCommMonObj B₀] (M₀ : LB B₀.left) (c₀ : Q.X → (Sp k₀ ⟶ B₀.left))
      (B' : Over (Sp K)) [GrpObj B'] (π₁ : B'.left ⟶ Q.P.A.left) (π₀ : B'.left ⟶ B₀.left)
      (w : LB.Iso (Q.P.L.pull π₁) (M₀.pull π₀)) (c' : Q.X → (Sp K ⟶ B'.left)),
      IsAbelianScheme B₀ → M₀.IsLB → IsGrpPullback B' Q.P.A (spMap ev) π₁ → IsGrpPullback B' B₀ (spMap k₀.subtype) π₀ →
      w.IsGen →
      (∀ a, c' a ≫ B'.hom = 𝟙 _ ∧ c' a ≫ π₁ = spMap ev ≫ (Q.c a).left ∧ c' a ≫ π₀ = spMap k₀.subtype ≫ c₀ a) →
      ∀ (a b : Q.X) (τ₁ : LB.Gen (LB.LinComb M₀ (K := Fin 4) ![c₀ (a + b), c₀ a, c₀ b, c₀ 0] ![-1, 1, 1, -1])),
        τ₁.IsGen → ∃ x : k₀ˣ, ∀ z J J₀, Good Q.P.L z J → Good M₀ z J₀ →
          val (τ₀ a b) (spMap ev) z J = lamUnit w c' a b z J J₀ *
            gm (𝟙 (Sp K)) z ⊤ (unitOn (Units.map k₀.subtype.toMonoidHom x)) * val τ₁ (spMap k₀.subtype) z J₀ := by
  intro R _ _ Q τ₀ K _ _ ev k₀ hk W₀ _ ιb hF hι B₀ _ _ M₀ c₀ B' _ π₁ π₀ w c' h₀ hM₀ p₁ p₀ hw hc a b τ₁ hτ
  obtain ⟨B₁, _, M₁, c₁, τ', β, w', h₁, hM₁, pβ, hw', -, -, hv'⟩ := hF
  let i : Sp K ⟶ Sp k₀ := spMap k₀.subtype
  let e₀ : W₀ →+* k₀ := (ev.comp ιb).codRestrict k₀ hι
  have he : spMap ev ≫ spMap ιb = i ≫ spMap e₀ :=
    (Spec.map_comp _ _).symm.trans (Spec.map_comp (CommRingCat.ofHom e₀) (CommRingCat.ofHom k₀.subtype))
  obtain ⟨κ₀, hκ⟩ := exists_descent k₀ (spMap e₀) B₀ B₁ B' h₀ h₁ p₀ ((p₁.comp pβ).congr he rfl)
  obtain ⟨v, hv⟩ := exists_lbIso k₀ B₀ B' h₀ p₀ hκ Q.P.isLB hM₀ hM₁ ⟨w, hw⟩ ⟨w', hw'⟩
  obtain ⟨ρ, hρ⟩ := exists_unit hκ Q.P.isLB hM₀ hM₁ hw hw' hv
  have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  let z₀ : Sp K := (default : PrimeSpectrum K)
  choose J₁ hJ₁ using fun χ : Sp K ⟶ B₁.left => exists_chart hM₁ (χ z₀)
  have gJ₁ : Good M₁ (spMap ev z₀) (fun χ => J₁ (spMap ev ≫ χ)) := fun χ => hJ₁ (spMap ev ≫ χ)
  let m : Q.X → M₁.ι := fun y => J₁ (spMap ev ≫ cpt Q y ≫ β)
  have hm₁ : ∀ y, β (π₁ (c' y z₀)) ∈ M₁.U (m y) := fun y => by
    have := hJ₁ (spMap ev ≫ cpt Q y ≫ β)
    rw [← Category.assoc] at this
    exact (congrArg (fun q : Sp K ⟶ _ => β (q z₀) ∈ M₁.U (m y)) (hc y).2.1).mpr this
  have hm₀ : ∀ y, κ₀ (c₀ y (i z₀)) ∈ M₁.U (m y) := fun y => by
    have e : i ≫ c₀ y ≫ κ₀ = c' y ≫ π₁ ≫ β := by rw [← hκ, ← Category.assoc, ← (hc y).2.2, Category.assoc]
    exact (congrArg (fun q : Sp K ⟶ _ => q z₀ ∈ M₁.U (m y)) e).mpr (hm₁ y)
  have mτ := gJ₁.mem ![c₁ (a + b), c₁ a, c₁ b, c₁ 0] (spMap ιb)
  let t := Units.map ((spMap ev).stalkMap z₀).hom.toMonoidHom
    (val (τ' a b) (spMap ιb) (spMap ev z₀) (fun χ => J₁ (spMap ev ≫ χ)))
  have ht : t ∈ (gm i z₀ ⊤).range := by
    have hp : spMap ιb (spMap ev z₀) = spMap e₀ (i z₀) := congrArg (fun q : Sp K ⟶ Sp W₀ => q z₀) he
    have hm' := Eq.mp (congrArg (· ∈ _) hp) mτ
    have e₄ : t = _ := SepBModel.stalkMap_gm (spMap ev) (spMap ιb) z₀ _ mτ _
    rw [he] at e₄
    replace e₄ := e₄.trans (gm_pull _ _ z₀ _ hm' _).symm
    obtain ⟨x, hx⟩ := SepBModel.gm_field i z₀ _ hm' (pullU (spMap e₀) _ ((τ' a b).s _))
    exact ⟨_, (e₄.trans hx).symm⟩
  obtain ⟨x, hx⟩ := exists_const k₀ hM₀ hM₁ hv _ τ₁ hτ z₀ ![m (a + b), m a, m b, m 0]
    (fun k => by fin_cases k <;> exact hm₀ _) t ht
  refine ⟨x, fun z J J₀ hJ hJ₀ => ?_⟩
  obtain rfl : z₀ = z := Subsingleton.elim _ _
  have gJ : Good Q.P.L (spMap ev z₀) (fun χ => J (spMap ev ≫ χ)) := fun χ => hJ (spMap ev ≫ χ)
  have E := congrArg (Units.map ((spMap ev).stalkMap z₀).hom.toMonoidHom) (hv' a b _ _ _ gJ gJ₁)
  have l : Units.map ((spMap ev).stalkMap z₀).hom.toMonoidHom
      (val (τ₀ a b) (𝟙 (Sp R)) (spMap ev z₀) (fun χ => J (spMap ev ≫ χ))) = val (τ₀ a b) (spMap ev) z₀ J := by
    refine (SepBModel.stalkMap_gm (spMap ev) (𝟙 _) z₀ _ (gJ.mem _ _) _).trans ?_
    rw [Category.comp_id]
    exact (val_of _ _ _ _ _ fun k => by rw [Category.id_comp]).symm
  have key : ∀ y, Units.map ((spMap ev).stalkMap z₀).hom.toMonoidHom
      (gm (cpt Q y) (spMap ev z₀) _ (w'.s (fun _ => J₁ (spMap ev ≫ cpt Q y ≫ β), J (spMap ev ≫ cpt Q y)))) =
      gm (c' 0) z₀ ⊤ ρ * gw v (i ≫ c₀ y) z₀ (m y) (J₀ (i ≫ c₀ y)) *
        gw w (c' y) z₀ (J₀ (c' y ≫ π₀)) (fun _ => J (c' y ≫ π₁)) := fun y => by
    have hmem : cpt Q y (spMap ev z₀) ∈ (M₁.pull β).U (fun _ => m y) ⊓ Q.P.L.U (J (spMap ev ≫ cpt Q y)) :=
      ⟨mem_pull.2 (gJ₁ (cpt Q y ≫ β)), gJ (cpt Q y)⟩
    refine (SepBModel.stalkMap_gm (spMap ev) (cpt Q y) z₀ _ hmem _).trans ?_
    have r := hρ _ (c' y) z₀ (J (c' y ≫ π₁)) (J₀ (c' y ≫ π₀)) (m y) (hJ (c' y ≫ π₁)) (hJ₀ (c' y ≫ π₀)) (hm₁ y)
    rw [gm_const i B₀ B' h₀ p₀ ρ z₀ (c' y) (c' 0) (hc y).1 (hc 0).1] at r
    have e₁ : c' y ≫ π₁ = spMap ev ≫ cpt Q y := (hc y).2.1
    have e₂ : c' y ≫ π₀ = i ≫ c₀ y := (hc y).2.2
    rw [← e₂, ← r, e₁]
    rfl
  rw [l, map_mul, map_mul, map_mul, map_mul, map_inv, map_inv] at E
  have E' := E.trans (congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·) (key _)
    (congrArg (·⁻¹) (key _))) (congrArg (·⁻¹) (key _))) (key _)) (rfl : _ = t))
  have hx' := hx J₀ hJ₀
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at hx'
  rw [E', _root_.mul_assoc (lamUnit _ _ _ _ _ _ _), ← hx', lamUnit]
  generalize gm (c' 0) z₀ ⊤ ρ = s
  simp only [mul_inv]
  rw [show ∀ a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ u, s * a₁ * b₁ * (s⁻¹ * a₂ * b₂) * (s⁻¹ * a₃ * b₃) * (s * a₄ * b₄) * u =
    (s * s⁻¹) * (s * s⁻¹) * (b₁ * b₂ * b₃ * b₄ * (a₁ * a₂ * a₃ * a₄ * u)) from fun _ _ _ _ _ _ _ _ _ => by ac_rfl]
  simp only [mul_inv_cancel, _root_.one_mul]
  rfl

end GlobalTheory.UCanon.BaseDescent
