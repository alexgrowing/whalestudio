import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMumfordFamOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMinAt
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.SiegJoin
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.GenTransport

variable {S' Z : Scheme.{0}} {π : S' ⟶ Z} {M : LB Z} {L : LB S'} {N : ℕ}

theorem w_trans (w : LB.Iso (M.pull π) (lbPow L N)) (hw : w.IsGen) {Y : Scheme.{0}} (f : Y ⟶ S') (y : Y)
    (i i' : L.ι) (k k' : M.ι) (hi : f y ∈ L.U i) (hi' : f y ∈ L.U i') (hk : (f ≫ π) y ∈ M.U k)
    (hk' : (f ≫ π) y ∈ M.U k') :
    gm f y ((lbPow L N).U (fun _ => i) ⊓ (M.pull π).U (fun _ => k)) (w.s (fun _ => i, fun _ => k)) =
      gm f y (L.U i ⊓ L.U i') (L.g i i') ^ (N : ℤ) * (gm (f ≫ π) y (M.U k ⊓ M.U k') (M.g k k'))⁻¹ *
        gm f y ((lbPow L N).U (fun _ => i') ⊓ (M.pull π).U (fun _ => k')) (w.s (fun _ => i', fun _ => k')) := by
  have m1 : f y ∈ (lbPow L N).U (fun _ => i) := Set.mem_iInter.2 fun _ => hi
  have m1' : f y ∈ (lbPow L N).U (fun _ => i') := Set.mem_iInter.2 fun _ => hi'
  have m2 : f y ∈ (M.pull π).U (fun _ => k) := Set.mem_iInter.2 fun _ => hk
  have m2' : f y ∈ (M.pull π).U (fun _ => k') := Set.mem_iInter.2 fun _ => hk'
  have hm : f y ∈ (lbPow L N).U (fun _ => i) ⊓ (M.pull π).U (fun _ => k) ⊓
      ((lbPow L N).U (fun _ => i') ⊓ (M.pull π).U (fun _ => k')) := ⟨⟨m1, m2⟩, ⟨m1', m2'⟩⟩
  have e := congrArg (gm f y ((lbPow L N).U (fun _ => i) ⊓ (M.pull π).U (fun _ => k) ⊓
      ((lbPow L N).U (fun _ => i') ⊓ (M.pull π).U (fun _ => k')))) (hw (fun _ => i, fun _ => k) (fun _ => i', fun _ => k'))
  have e1 : gm f y ((lbPow L N).U (fun _ => i) ⊓ (M.pull π).U (fun _ => k)) (w.s (fun _ => i, fun _ => k)) =
      gm f y ((lbPow L N).U (fun _ => i) ⊓ (M.pull π).U (fun _ => k) ⊓
      ((lbPow L N).U (fun _ => i') ⊓ (M.pull π).U (fun _ => k'))) (res inf_le_left (w.s (fun _ => i, fun _ => k))) :=
    (gm_res f y _ hm _).symm
  have e2 : gm f y ((lbPow L N).U (fun _ => i) ⊓ (M.pull π).U (fun _ => k) ⊓
      ((lbPow L N).U (fun _ => i') ⊓ (M.pull π).U (fun _ => k'))) (res inf_le_right (w.s (fun _ => i', fun _ => k'))) =
      gm f y ((lbPow L N).U (fun _ => i') ⊓ (M.pull π).U (fun _ => k')) (w.s (fun _ => i', fun _ => k')) :=
    gm_res f y _ hm _
  have e3 := gm_div (M.pull π) (lbPow L N) f y (fun _ => i, fun _ => k) (fun _ => i', fun _ => k') hm
  refine e1.trans (e.trans ((MonoidHom.map_mul _ _ _).trans (congrArg₂ (· * ·) (e3.trans ?_) e2)))
  exact congrArg₂ (fun a b => a * b⁻¹)
    ((gm_linComb L (fun _ => 𝟙 S') (fun _ => (N : ℤ)) f y (fun _ => i) (fun _ => i') m1 m1').trans
      (by rw [Fintype.prod_unique, Category.comp_id]))
    (gm_pull_g M π f y (fun _ => k) (fun _ => k') m2 m2')

theorem alg₁ {G : Type*} [CommGroup G] (t E W : G) (N : ℕ) :
    (t * E) ^ N * (t ^ (N : ℤ) * 1⁻¹ * W)⁻¹ = E ^ N * W⁻¹ := by
  rw [zpow_natCast, inv_one, _root_.mul_one, _root_.mul_pow, _root_.mul_inv, _root_.mul_comm (t ^ N),
    _root_.mul_assoc, mul_inv_cancel_left]

theorem alg₂ {G : Type*} [CommGroup G] (E g W : G) (N : ℕ) :
    E ^ N * ((1 : G) ^ (N : ℤ) * g⁻¹ * W)⁻¹ = g * (E ^ N * W⁻¹) := by
  rw [one_zpow, _root_.one_mul, _root_.mul_inv, inv_inv, _root_.mul_left_comm]

theorem exists_strictHenselian_absolutely_closed_local_ring (hL : L.IsLB) (hM : M.IsLB) (w : LB.Iso (M.pull π) (lbPow L N)) (hw : w.IsGen)
    {A : Scheme.{0}} (a : A ⟶ S') (e : LB.Gen (L.pull a)) (he : e.IsGen) :
    ∃ t : LB.Gen (M.pull (a ≫ π)), t.IsGen ∧ ∀ (Y : Scheme.{0}) (r : Y ⟶ A) (z : Y) (i : L.ι) (k : M.ι),
      (r ≫ a) z ∈ L.U i → (r ≫ a ≫ π) z ∈ M.U k →
      gm r z ((M.pull (a ≫ π)).U (fun _ => k)) (t.s (fun _ => k)) =
        gm r z ((L.pull a).U (fun _ => i)) (e.s (fun _ => i)) ^ N *
          (gm (r ≫ a) z ((lbPow L N).U (fun _ => i) ⊓ (M.pull π).U (fun _ => k))
            (w.s (fun _ => i, fun _ => k)))⁻¹ := by
  have loc : ∀ k : M.ι, ∃ s : Γ(A, (M.pull (a ≫ π)).U (fun _ => k))ˣ, ∀ (Y : Scheme.{0}) (r : Y ⟶ A) (z : Y)
      (i : L.ι), (r ≫ a) z ∈ L.U i → (r ≫ a ≫ π) z ∈ M.U k →
      gm r z _ s = gm r z ((L.pull a).U (fun _ => i)) (e.s (fun _ => i)) ^ N *
          (gm (r ≫ a) z ((lbPow L N).U (fun _ => i) ⊓ (M.pull π).U (fun _ => k))
            (w.s (fun _ => i, fun _ => k)))⁻¹ := by
    intro k
    let V := (M.pull (a ≫ π)).U (fun _ => k)
    let W : L.ι → A.Opens := fun i => V ⊓ (L.pull a).U (fun _ => i)
    have h1 : ∀ i, W i ≤ (L.pull a).U (fun _ => i) := fun i => inf_le_right
    have h2 : ∀ i, W i ≤ a ⁻¹ᵁ ((lbPow L N).U (fun _ => i) ⊓ (M.pull π).U (fun _ => k)) := fun i x hx =>
      ⟨Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hx.2 (), Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hx.1 ()⟩
    let u : ∀ i, Γ(A, W i)ˣ := fun i =>
      res (h1 i) (e.s (fun _ => i)) ^ N * (res (h2 i) (pullU a _ (w.s (fun _ => i, fun _ => k))))⁻¹
    have hu : ∀ (Y : Scheme.{0}) (r : Y ⟶ A) (z : Y) (i : L.ι), r z ∈ W i →
        gm r z (W i) (u i) = gm r z ((L.pull a).U (fun _ => i)) (e.s (fun _ => i)) ^ N *
          (gm (r ≫ a) z ((lbPow L N).U (fun _ => i) ⊓ (M.pull π).U (fun _ => k))
            (w.s (fun _ => i, fun _ => k)))⁻¹ := by
      intro Y r z i hz
      simp only [u, map_mul, map_pow, map_inv]
      exact congrArg₂ (fun p q => p ^ N * q⁻¹) (gm_res r z (h1 i) hz _)
        ((gm_res r z (h2 i) hz _).trans (gm_pull r a z _ (h2 i hz) _))
    obtain ⟨s, hs⟩ := glue_unit V W (fun i => inf_le_left) (fun x hx => by
        obtain ⟨i, hi⟩ := exists_chart hL (a x)
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hx, Set.mem_iInter.2 fun _ => hi⟩) u
      (fun i j x hx => by
        have hi : (𝟙 A ≫ a) x ∈ L.U i := Set.mem_iInter.1 hx.1.2 ()
        have hj : (𝟙 A ≫ a) x ∈ L.U j := Set.mem_iInter.1 hx.2.2 ()
        have hk : ((𝟙 A ≫ a) ≫ π) x ∈ M.U k := Set.mem_iInter.1 hx.1.1 ()
        have g1 : gm (𝟙 A) x ((L.pull a).U fun _ => i) (e.s fun _ => i) =
            trF (fun _ : PUnit => a) (fun _ => 1) (𝟙 A) x (fun _ => i) (fun _ => j) *
              gm (𝟙 A) x ((L.pull a).U fun _ => j) (e.s fun _ => j) := gen_trans he (𝟙 A) x hx.1.2 hx.2.2
        rw [hu A (𝟙 A) x i hx.1, hu A (𝟙 A) x j hx.2, g1,
          w_trans w hw (𝟙 A ≫ a) x i j k k hi hj hk hk, gm_self hM _ x hk]
        simp only [trF, Fintype.prod_unique, zpow_one]
        exact alg₁ _ _ _ N)
    refine ⟨s, fun Y r z i hi hk => ?_⟩
    have hz : r z ∈ W i := ⟨Set.mem_iInter.2 fun _ => hk, Set.mem_iInter.2 fun _ => hi⟩
    rw [← gm_res r z (inf_le_left : W i ≤ V) hz, hs i, hu Y r z i hz]
  choose s hs using loc
  refine ⟨⟨fun k => s (k ())⟩, fun k k' => unit_ext fun x hx => ?_, fun Y r z i k hi hk => hs k Y r z i hi hk⟩
  refine (gm_res (𝟙 A) x _ hx _).trans (Eq.trans ?_ ((MonoidHom.map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_pull_g M (a ≫ π) (𝟙 A) x k k' hx.1 hx.2) (gm_res (𝟙 A) x _ hx _))).symm)
  obtain ⟨i, hi⟩ := exists_chart hL ((𝟙 A ≫ a) x)
  have hk : ((𝟙 A ≫ a) ≫ π) x ∈ M.U (k ()) := Set.mem_iInter.1 hx.1 ()
  have hk' : ((𝟙 A ≫ a) ≫ π) x ∈ M.U (k' ()) := Set.mem_iInter.1 hx.2 ()
  have v1 : gm (𝟙 A) x ((M.pull (a ≫ π)).U k) (s (k ())) = _ := hs (k ()) A (𝟙 A) x i hi hk
  have v2 : gm (𝟙 A) x ((M.pull (a ≫ π)).U k') (s (k' ())) = _ := hs (k' ()) A (𝟙 A) x i hi hk'
  rw [v1, v2, w_trans w hw (𝟙 A ≫ a) x i i (k ()) (k' ()) hi hi hk hk', gm_self hL (𝟙 A ≫ a) x hi, Category.assoc]
  exact alg₂ _ _ _ N

theorem transport : ∀ (S' Z : Scheme.{0}) (π : S' ⟶ Z) (M : LB Z) (L : LB S') (N : ℕ), M.IsLB → L.IsLB → LBIso (M.pull π) (lbPow L N) → ∃ T : ∀ (A : Scheme.{0}) (a : A ⟶ S'), LB.Gen (L.pull a) → LB.Gen (M.pull (a ≫ π)), (∀ (A : Scheme.{0}) (a : A ⟶ S') (e : LB.Gen (L.pull a)), e.IsGen → (T A a e).IsGen) ∧ ∀ (A A' Y : Scheme.{0}) (a : A ⟶ S') (a' : A' ⟶ S') (e : LB.Gen (L.pull a)) (e' : LB.Gen (L.pull a')) (r : Y ⟶ A) (r' : Y ⟶ A'), e.IsGen → e'.IsGen → r ≫ a = r' ≫ a' → (∀ (z : Y) (J : (Y ⟶ S') → L.ι), Good L z J → val (L := L) (φ := fun _ : PUnit => a) (ε := fun _ => 1) e r z J = val (L := L) (φ := fun _ : PUnit => a') (ε := fun _ => 1) e' r' z J) → ∀ (z : Y) (J : (Y ⟶ Z) → M.ι), Good M z J → val (L := M) (φ := fun _ : PUnit => a ≫ π) (ε := fun _ => 1) (T A a e) r z J = val (L := M) (φ := fun _ : PUnit => a' ≫ π) (ε := fun _ => 1) (T A' a' e') r' z J := by
  intro S' Z π M L N hM hL hw0
  obtain ⟨w, hw⟩ := hw0
  classical
  refine ⟨fun A a e => if he : e.IsGen then (exists_strictHenselian_absolutely_closed_local_ring hL hM w hw a e he).choose else ⟨fun _ => 1⟩,
    fun A a e he => ?_, ?_⟩
  · simp only [dif_pos he]
    exact (exists_strictHenselian_absolutely_closed_local_ring hL hM w hw a e he).choose_spec.1
  · intro A A' Y a a' e e' r r' he he' hr hval z J hJ
    simp only [dif_pos he, dif_pos he']
    have hk : (r ≫ a ≫ π) z ∈ M.U (J (r ≫ a ≫ π)) := hJ _
    have hk'e : J (r' ≫ a' ≫ π) = J (r ≫ a ≫ π) := by rw [← Category.assoc, ← hr, Category.assoc]
    have hk' : (r' ≫ a' ≫ π) z ∈ M.U (J (r ≫ a ≫ π)) := hk'e ▸ hJ _
    obtain ⟨i, hi⟩ := exists_chart hL ((r ≫ a) z)
    have hi' : (r' ≫ a') z ∈ L.U i := by rw [← hr]; exact hi
    obtain ⟨JL, hJL, eJL⟩ := exists_good L hL z (K := PUnit) (fun _ => r ≫ a) (fun _ => i)
      (fun _ _ _ => rfl) (fun _ => hi)
    have v1 := val_of (L := L) (φ := fun _ : PUnit => a) (ε := fun _ => 1) e r z JL (fun _ => i) (fun _ => eJL ())
    have v2 := val_of (L := L) (φ := fun _ : PUnit => a') (ε := fun _ => 1) e' r' z JL (fun _ => i)
      (fun _ => by rw [← hr]; exact eJL ())
    have hv := hval z JL hJL
    rw [v1, v2] at hv
    rw [val_of (L := M) (φ := fun _ : PUnit => a ≫ π) (ε := fun _ => 1) _ r z J (fun _ => J (r ≫ a ≫ π))
        (fun _ => rfl),
      val_of (L := M) (φ := fun _ : PUnit => a' ≫ π) (ε := fun _ => 1) _ r' z J (fun _ => J (r ≫ a ≫ π))
        (fun _ => hk'e),
]
    refine (((exists_strictHenselian_absolutely_closed_local_ring hL hM w hw a e he).choose_spec.2 Y r z i _ hi hk).trans ?_).trans
      ((exists_strictHenselian_absolutely_closed_local_ring hL hM w hw a' e' he').choose_spec.2 Y r' z i _ hi' hk').symm
    rw [hr]
    congr 1
    exact congrArg (· ^ N) hv

end GlobalTheory.GenTransport
