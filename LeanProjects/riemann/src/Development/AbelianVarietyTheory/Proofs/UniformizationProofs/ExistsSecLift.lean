import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfSmallExtension
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw (FirstCohomologyVanishes rs)
open GlobalTheory.SmallExtLift

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.SecLift

variable {X Y Z : Scheme.{0}} {A : Type} [CommRing A]

theorem surj_of_nil {A₀ : Type} [CommRing A₀] {g : A →+* A₀} (hg : Function.Surjective g)
    (hn : ∀ x ∈ RingHom.ker g, IsNilpotent x) {f : X ⟶ Spec (CommRingCat.of A)} {j : Y ⟶ X}
    {f₀ : Y ⟶ Spec (CommRingCat.of A₀)} (P : IsPullback j f₀ f (Spec.map (CommRingCat.ofHom g))) :
    Function.Surjective j := by
  have h : Surjective (Spec.map (CommRingCat.ofHom g)) := ⟨fun p => by
    have : p ∈ Set.range (PrimeSpectrum.comap g) := by
      rw [range_comap_of_surjective _ g hg]
      intro x hx
      obtain ⟨n, hx⟩ := hn x hx
      exact p.isPrime.mem_of_pow_mem n (by rw [hx]; exact Ideal.zero_mem _)
    exact this⟩
  exact (MorphismProperty.of_isPullback (P := @Surjective) P.flip h).1

theorem inducing_of_surj {A₀ : Type} [CommRing A₀] {g : A →+* A₀} (hg : Function.Surjective g)
    {f : X ⟶ Spec (CommRingCat.of A)} {j : Y ⟶ X}
    {f₀ : Y ⟶ Spec (CommRingCat.of A₀)} (P : IsPullback j f₀ f (Spec.map (CommRingCat.ofHom g))) :
    Topology.IsInducing j := by
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom g)) :=
    IsClosedImmersion.spec_of_surjective _ hg
  have : IsClosedImmersion j := MorphismProperty.of_isPullback P.flip this
  exact j.isClosedEmbedding.isInducing

theorem exists_open {F : Y ⟶ X} (hF : Topology.IsInducing F) {y : Y} {O : Y.Opens} (hy : y ∈ O) :
    ∃ U : X.Opens, F y ∈ U ∧ F ⁻¹ᵁ U ≤ O := by
  obtain ⟨U, hU, e⟩ := hF.isOpen_iff.1 O.isOpen
  refine ⟨⟨U, hU⟩, ?_, fun z hz => ?_⟩
  · exact (Set.ext_iff.1 e y).2 hy
  · exact (Set.ext_iff.1 e z).1 hz

theorem exists_affine_zero {F : Y ⟶ X} (hF : Topology.IsInducing F) (y : Y) (U : X.Opens)
    (h : (𝟙 Y ≫ F) y ∈ U) (s : Γ(X, U)) (hs : gr (𝟙 Y ≫ F) y U h s = 0) :
    ∃ (V : X.Opens) (hle : V ≤ U), IsAffineOpen V ∧ F y ∈ V ∧ (F.app V).hom (rs X hle s) = 0 := by
  obtain ⟨W, hW, iU, iV, e⟩ := Y.presheaf.germ_eq (U := F ⁻¹ᵁ U) (V := F ⁻¹ᵁ U) y h h
    ((F.app U).hom s) 0 (hs.trans (map_zero _).symm)
  obtain ⟨O, hO, hle⟩ := exists_open hF hW
  obtain ⟨V, hV, hxV, hl⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
    (show F y ∈ O ⊓ U from ⟨hO, h⟩)
  refine ⟨V, hl.trans inf_le_right, hV, hxV, gr_ext fun z hz => ?_⟩
  have hz' : (𝟙 Y : Y ⟶ Y) z ∈ W := hle (hl hz).1
  rw [gr_app, gr_res, map_zero, ← gr_app (𝟙 Y) F z U (hl hz).2, ← gr_res (𝟙 Y) z iU.le hz']
  exact (congrArg (gr (𝟙 Y) z W hz') (e.trans (map_zero _))).trans (map_zero _)

theorem stalkMap_gr (j : Y ⟶ X) (y : Y) (U : X.Opens) (h : j y ∈ U) (s : Γ(X, U)) :
    (j.stalkMap y).hom (gr (𝟙 X) (j y) U h s) = gr (𝟙 Y ≫ j) y U h s :=
  j.germ_stalkMap_apply U y h s

theorem mem_of_flat' {a : A} {I : Ideal A} (hI : ∀ x, a * x = 0 → x ∈ I) {B : Type} [CommRing B]
    (c : A →+* B) (hf : c.Flat) (b : B) (hb : c a * b = 0) : b ∈ I.map c := by
  letI := c.toAlgebra
  haveI : Module.Flat A B := hf
  obtain ⟨l, d, y, hy, hc⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := A) (M := B)
    (f := fun _ : Unit => a) (x := fun _ => b)
    (by rw [Fintype.sum_unique, Algebra.smul_def]; exact hb)
  have : b = ∑ j, d () j • y j := hy ()
  rw [this]
  refine Ideal.sum_mem _ fun j _ => ?_
  rw [Algebra.smul_def]
  refine Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem c (hI _ ?_))
  have h := hc j
  rwa [Fintype.sum_unique] at h

theorem stalk_iff {A₀ : Type} [CommRing A₀] {g : A →+* A₀} (hg : Function.Surjective g) {a : A}
    (ha : ∀ x, a * x = 0 ↔ x ∈ RingHom.ker g) {f : X ⟶ Spec (CommRingCat.of A)} [Flat f]
    {j : Y ⟶ X} {f₀ : Y ⟶ Spec (CommRingCat.of A₀)}
    (P : IsPullback j f₀ f (Spec.map (CommRingCat.ofHom g))) (y : Y)
    (e : X.presheaf.stalk (j y)) :
    cstS (𝟙 X ≫ f) (j y) a * e = 0 ↔ (j.stalkMap y).hom e = 0 := by
  obtain ⟨U, h, s, rfl⟩ := X.presheaf.exists_germ_eq e
  change _ * gr (𝟙 X) (j y) U h s = 0 ↔ (j.stalkMap y).hom (gr (𝟙 X) (j y) U h s) = 0
  rw [stalkMap_gr]
  constructor
  · intro H
    rw [← gr_cst (𝟙 X) f (j y) U h, ← map_mul] at H
    obtain ⟨V, hle, hV, hy, e⟩ := exists_affine_zero (F := 𝟙 X) Topology.IsInducing.id (j y) U h _ H
    have e' : cst f V a * rs X hle s = 0 := gr_ext fun x hx => by
      have := congrArg (gr (𝟙 X) x V hx) (show rs X hle (cst f U a * s) = 0 from e)
      rw [gr_res, map_mul, gr_cst] at this
      rw [map_mul, gr_res, gr_cst, this]
    have hm := mem_of_flat' (fun x => (ha x).1) _ (cst_flat f hV) _ e'
    have e₀ : (j.app V).hom (rs X hle s) = 0 := by
      refine (show _ ≤ RingHom.ker (j.app V).hom from Ideal.map_le_iff_le_comap.2 fun r hr => ?_) hm
      rw [Ideal.mem_comap, RingHom.mem_ker, app_cst P.w, (RingHom.mem_ker).1 hr, map_zero]
    rw [← gr_res (𝟙 Y ≫ j) y hle hy, ← gr_app (𝟙 Y) j y V hy, e₀, map_zero]
  · intro H
    obtain ⟨V, hle, hV, hy, e⟩ := exists_affine_zero (inducing_of_surj hg P) y U h s H
    have := mul_eq_zero_of_mem (cst f V) (ε := a) (fun x hx => by rw [mul_comm]; exact (ha x).2 hx)
      (mem_of_app_eq_zero hg P hV _ e)
    rw [← gr_res (𝟙 X) (j y) hle hy, ← gr_cst (𝟙 X) f (j y) V hy, ← map_mul, this, map_zero]

theorem exists_div {f : X ⟶ Spec (CommRingCat.of A)} {j : Y ⟶ X} {a : A}
    (hS : ∀ (y : Y) (e : X.presheaf.stalk (j y)),
      cstS (𝟙 X ≫ f) (j y) a * e = 0 → (j.stalkMap y).hom e = 0)
    (W : X.Opens) (d : Γ(X, W))
    (hd : ∀ (V : X.Opens) (hle : V ≤ W), IsAffineOpen V → ∃ e, rs X hle d = cst f V a * e) :
    ∃ φ : Γ(Y, j ⁻¹ᵁ W), ∀ (y : Y) (h : j y ∈ W), ∃ e, gr (𝟙 X) (j y) W h d =
      cstS (𝟙 X ≫ f) (j y) a * e ∧ (j.stalkMap y).hom e = gr (𝟙 Y) y (j ⁻¹ᵁ W) h φ := by
  let I := {V : X.Opens // IsAffineOpen V ∧ V ≤ W}
  choose e he using fun V : I => hd V.1 V.2.2 V.2.1
  have he' : ∀ (V : I) (x : X) (h : x ∈ V.1), gr (𝟙 X) x W (V.2.2 h) d =
      cstS (𝟙 X ≫ f) x a * gr (𝟙 X) x V.1 h (e V) := fun V x h => by
    rw [← gr_res (𝟙 X) x V.2.2 h, ← gr_cst (𝟙 X) f x V.1 h, ← map_mul, ← he]
  have cov : ∀ x ∈ W, ∃ V : I, x ∈ V.1 := fun x hx => by
    obtain ⟨V, hV, hxV, hl⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens hx
    exact ⟨⟨V, hV, hl⟩, hxV⟩
  obtain ⟨φ, hφ, -⟩ := Y.sheaf.existsUnique_gluing' (fun V : I => j ⁻¹ᵁ V.1) (j ⁻¹ᵁ W)
    (fun V => homOfLE (fun _ h => V.2.2 h)) (fun y hy => Opens.mem_iSup.2 (cov _ hy))
    (fun V => (j.app V.1).hom (e V))
    (fun V V' => gr_ext (V := j ⁻¹ᵁ V.1 ⊓ j ⁻¹ᵁ V'.1) fun y hy => by
      refine (gr_res _ y inf_le_left hy _).trans (Eq.trans ?_ (gr_res _ y inf_le_right hy _).symm)
      rw [gr_app, gr_app, ← stalkMap_gr, ← stalkMap_gr, ← sub_eq_zero, ← map_sub]
      refine hS y _ ?_
      rw [mul_sub, ← he' V (j y) hy.1, ← he' V' (j y) hy.2, sub_self])
  refine ⟨φ, fun y h => ?_⟩
  obtain ⟨V, hV⟩ := cov _ h
  refine ⟨_, he' V _ hV, ?_⟩
  rw [stalkMap_gr, ← gr_app (𝟙 Y) j y V.1 hV]
  exact (congrArg (gr (𝟙 Y) y _ hV) (hφ V)).symm.trans (gr_res (𝟙 Y) y _ hV φ)

theorem sec_of_refine {M : LB X} (hM : M.IsLB) {I : Type} (V : I → X.Opens)
    (cov : ∀ x : X, ∃ a, x ∈ V a)
    (j : I → M.ι) (hj : ∀ a, V a ≤ M.U (j a)) (w : ∀ a, Γ(X, V a))
    (H : ∀ a b x (ha : (𝟙 X : X ⟶ X) x ∈ V a) (hb : (𝟙 X : X ⟶ X) x ∈ V b),
      gr (𝟙 X) x _ ha (w a) = gr (𝟙 X) x (M.U (j a) ⊓ M.U (j b)) ⟨hj a ha, hj b hb⟩
        (M.g (j a) (j b)).val * gr (𝟙 X) x _ hb (w b)) :
    ∃ s : LB.Sec M, ∀ i a (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (hi : r z ∈ M.U i) (ha : r z ∈ V a),
      gr r z _ hi (s.f i) =
        gr r z (M.U i ⊓ M.U (j a)) ⟨hi, hj a ha⟩ (M.g i (j a)).val * gr r z _ ha (w a) := by
  have glue : ∀ i : M.ι, ∃ s : Γ(X, M.U i), ∀ a (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z)
      (hi : r z ∈ M.U i) (ha : r z ∈ V a), gr r z _ hi s =
        gr r z (M.U i ⊓ M.U (j a)) ⟨hi, hj a ha⟩ (M.g i (j a)).val * gr r z _ ha (w a) := by
    intro i
    let u : ∀ a, Γ(X, M.U i ⊓ V a) := fun a =>
      (X.presheaf.map (homOfLE (inf_le_inf_left _ (hj a))).op).hom (M.g i (j a)).val *
        (X.presheaf.map (homOfLE inf_le_right).op).hom (w a)
    have hu : ∀ a (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (h : r z ∈ M.U i ⊓ V a), gr r z _ h (u a) =
        gr r z (M.U i ⊓ M.U (j a)) ⟨h.1, hj a h.2⟩ (M.g i (j a)).val *
          gr r z _ h.2 (w a) := fun a Z r x h =>
      (map_mul _ _ _).trans (congrArg₂ (· * ·) (gr_res _ x _ h _) (gr_res _ x _ h _))
    obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' (fun a => M.U i ⊓ V a) (M.U i)
      (fun a => homOfLE inf_le_left) (fun x hx => by
        obtain ⟨a, ha⟩ := cov x
        exact Opens.mem_iSup.2 ⟨a, hx, ha⟩) u
      (fun a b => gr_ext (V := (M.U i ⊓ V a) ⊓ (M.U i ⊓ V b)) fun x hx => by
        refine (gr_res _ x inf_le_left hx _).trans
          (Eq.trans ?_ (gr_res _ x inf_le_right hx _).symm)
        refine (hu a _ _ x hx.1).trans (Eq.trans ?_ (hu b _ _ x hx.2).symm)
        rw [H a b x hx.1.2 hx.2.2, ← _root_.mul_assoc,
          gr_cocycle hM _ x hx.1.1 (hj a hx.1.2) (hj b hx.2.2)])
    refine ⟨s, fun a Z r x hi ha => ?_⟩
    have hm : r x ∈ M.U i ⊓ V a := ⟨hi, ha⟩
    exact (gr_res _ x inf_le_left hm s).symm.trans
      ((congrArg (gr _ x _ hm) (hs a)).trans (hu a _ r x hm))
  choose s hs using glue
  refine ⟨⟨s, fun i k => gr_ext fun x hx => ?_⟩, hs⟩
  obtain ⟨a, ha⟩ := cov x
  refine (gr_res _ x inf_le_left hx (s i)).trans (Eq.trans ?_ ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) rfl (gr_res _ x inf_le_right hx (s k)))).symm)
  rw [hs i a _ _ x hx.1 ha, hs k a _ _ x hx.2 ha, ← _root_.mul_assoc,
    ← gr_cocycle hM _ x hx.1 hx.2 (hj a ha)]

section Iso
variable {N : LB X} {N' : LB Y} {F : Y ⟶ X}

theorem iso_rel {w : LB.Iso N' (N.pull F)} (hw : w.IsGen) (y : Y) {k l : N.ι} {k' l' : N'.ι}
    (hk : F y ∈ N.U k) (hl : F y ∈ N.U l) (hk' : y ∈ N'.U k') (hl' : y ∈ N'.U l') :
    (Geo.Tor.gw w (𝟙 Y) y k k').val * gr (𝟙 Y) y (N'.U k' ⊓ N'.U l') ⟨hk', hl'⟩ (N'.g k' l').val =
      gr (𝟙 Y ≫ F) y (N.U k ⊓ N.U l) ⟨hk, hl⟩ (N.g k l).val * (Geo.Tor.gw w (𝟙 Y) y l l').val := by
  have h := (isGen_iff w).1 hw _ (𝟙 Y) y k l k' l' hk hl hk' hl'
  have e₁ := gm_val (𝟙 Y) y (N'.U k' ⊓ N'.U l') ⟨hk', hl'⟩ (N'.g k' l')
  have e₂ := gm_val (𝟙 Y ≫ F) y (N.U k ⊓ N.U l) ⟨hk, hl⟩ (N.g k l)
  refine (congrArg _ e₁.symm).trans (Eq.trans ?_ (congrArg (· * _) e₂))
  rw [h, ← Units.val_mul, ← Units.val_mul, mul_right_comm, inv_mul_cancel_right]

theorem exists_unit (w : LB.Iso N' (N.pull F)) (k : N.ι) (k' : N'.ι) {V : X.Opens}
    (h : V ≤ N.U k) (h' : F ⁻¹ᵁ V ≤ N'.U k') :
    ∃ ω : Γ(Y, F ⁻¹ᵁ V)ˣ, ∀ (y : Y) (hy : F y ∈ V),
      gr (𝟙 Y) y (F ⁻¹ᵁ V) hy ω.val = (Geo.Tor.gw w (𝟙 Y) y k k').val :=
  ⟨res (le_inf (pull_le N F k h) h') (w.s (fun _ => k, k')), fun y hy =>
    (gm_val (𝟙 Y) y (F ⁻¹ᵁ V) hy _).symm.trans (congrArg Units.val (gm_res (𝟙 Y) y _ hy _))⟩

theorem sec_rel (s : LB.Sec N) (x : X) {k l : N.ι} (hk : x ∈ N.U k) (hl : x ∈ N.U l) :
    gr (𝟙 X) x _ hk (s.f k) =
      gr (𝟙 X) x (N.U k ⊓ N.U l) ⟨hk, hl⟩ (N.g k l).val * gr (𝟙 X) x _ hl (s.f l) := by
  have := congrArg (gr (𝟙 X) x (N.U k ⊓ N.U l) ⟨hk, hl⟩) (s.compat k l)
  rwa [map_mul, gr_res, gr_res] at this

theorem split_cocycle {w : LB.Iso N' (N.pull F)} (hw : w.IsGen) (H : FirstCohomologyVanishes N') {I : Type}
    (V : I → X.Opens) (cov : ∀ x : X, ∃ a, x ∈ V a) (k : I → N.ι) (k' : I → N'.ι)
    (h : ∀ a, V a ≤ N.U (k a)) (h' : ∀ a, F ⁻¹ᵁ V a ≤ N'.U (k' a))
    (φ : ∀ a b, Γ(Y, F ⁻¹ᵁ (V a ⊓ V b)))
    (hφ : ∀ a b d (y : Y) (ha : F y ∈ V a) (hb : F y ∈ V b) (hd : F y ∈ V d),
      gr (𝟙 Y) y (F ⁻¹ᵁ (V a ⊓ V b)) ⟨ha, hb⟩ (φ a b) +
        gr (𝟙 Y ≫ F) y (N.U (k a) ⊓ N.U (k b)) ⟨h a ha, h b hb⟩ (N.g (k a) (k b)).val *
          gr (𝟙 Y) y (F ⁻¹ᵁ (V b ⊓ V d)) ⟨hb, hd⟩ (φ b d) =
        gr (𝟙 Y) y (F ⁻¹ᵁ (V a ⊓ V d)) ⟨ha, hd⟩ (φ a d)) :
    ∃ ψ : ∀ a, Γ(Y, F ⁻¹ᵁ V a), ∀ a b (y : Y) (ha : F y ∈ V a) (hb : F y ∈ V b),
      gr (𝟙 Y) y (F ⁻¹ᵁ (V a ⊓ V b)) ⟨ha, hb⟩ (φ a b) = gr (𝟙 Y) y (F ⁻¹ᵁ V a) ha (ψ a) -
        gr (𝟙 Y ≫ F) y (N.U (k a) ⊓ N.U (k b)) ⟨h a ha, h b hb⟩ (N.g (k a) (k b)).val *
          gr (𝟙 Y) y (F ⁻¹ᵁ V b) hb (ψ b) := by
  choose ω hω using fun a => exists_unit w (k a) (k' a) (h a) (h' a)
  have hi : ∀ a (y : Y) (ha : F y ∈ V a), (Geo.Tor.gw w (𝟙 Y) y (k a) (k' a)).val *
      gr (𝟙 Y) y (F ⁻¹ᵁ V a) ha (ω a)⁻¹.val = 1 := fun a y ha => by
    rw [← hω a y ha, ← map_mul, Units.mul_inv, map_one]
  let χ : ∀ a b, Γ(Y, F ⁻¹ᵁ V a ⊓ F ⁻¹ᵁ V b) := fun a b => rs Y inf_le_left (ω a)⁻¹.val *
    rs Y (show F ⁻¹ᵁ V a ⊓ F ⁻¹ᵁ V b ≤ F ⁻¹ᵁ (V a ⊓ V b) from fun _ h => h) (φ a b)
  have hχ : ∀ a b (y : Y) (hy : y ∈ F ⁻¹ᵁ V a ⊓ F ⁻¹ᵁ V b), gr (𝟙 Y) y _ hy (χ a b) =
      gr (𝟙 Y) y (F ⁻¹ᵁ V a) hy.1 (ω a)⁻¹.val * gr (𝟙 Y) y (F ⁻¹ᵁ (V a ⊓ V b)) hy (φ a b) :=
    fun a b y hy => (map_mul _ _ _).trans (congrArg₂ (· * ·) (gr_res _ y _ hy _) (gr_res _ y _ hy _))
  clear_value χ
  obtain ⟨ψ, hψ⟩ := H I (fun a => F ⁻¹ᵁ V a) k' h'
    (eq_top_iff.2 fun y _ => Opens.mem_iSup.2 (cov (F y))) χ (fun a b d => gr_ext fun y hy => by
      rw [map_add, gr_res, gr_res, map_mul, gr_res, gr_res, hχ, hχ, hχ]
      have e₁ := hφ a b d y hy.1.1 hy.1.2 hy.2
      have e₂ := iso_rel hw y (h a hy.1.1) (h b hy.1.2) (h' a hy.1.1) (h' b hy.1.2)
      have e₃ := hi a y hy.1.1
      have e₄ := hi b y hy.1.2
      refine (Units.isUnit (Geo.Tor.gw w (𝟙 Y) y (k a) (k' a))).mul_left_cancel ?_
      linear_combination e₁ + (gr (𝟙 Y) y (F ⁻¹ᵁ (V a ⊓ V b)) hy.1 (φ a b) -
        gr (𝟙 Y) y (F ⁻¹ᵁ (V a ⊓ V d)) ⟨hy.1.1, hy.2⟩ (φ a d)) * e₃ +
        (gr (𝟙 Y) y (F ⁻¹ᵁ V b) hy.1.2 (ω b)⁻¹.val *
          gr (𝟙 Y) y (F ⁻¹ᵁ (V b ⊓ V d)) ⟨hy.1.2, hy.2⟩ (φ b d)) * e₂ +
        (gr (𝟙 Y ≫ F) y (N.U (k a) ⊓ N.U (k b)) ⟨h a hy.1.1, h b hy.1.2⟩ (N.g (k a) (k b)).val *
          gr (𝟙 Y) y (F ⁻¹ᵁ (V b ⊓ V d)) ⟨hy.1.2, hy.2⟩ (φ b d)) * e₄)
  refine ⟨fun a => (ω a).val * ψ a, fun a b y ha hb => ?_⟩
  have e₁ := congrArg (gr (𝟙 Y) y (F ⁻¹ᵁ V a ⊓ F ⁻¹ᵁ V b) ⟨ha, hb⟩) (hψ a b)
  rw [hχ, map_sub, map_mul, gr_res, gr_res, gr_res] at e₁
  have e₂ := iso_rel hw y (h a ha) (h b hb) (h' a ha) (h' b hb)
  have e₃ := hi a y ha
  rw [map_mul, map_mul, hω, hω]
  linear_combination (Geo.Tor.gw w (𝟙 Y) y (k a) (k' a)).val * e₁ -
    gr (𝟙 Y) y (F ⁻¹ᵁ (V a ⊓ V b)) ⟨ha, hb⟩ (φ a b) * e₃ - gr (𝟙 Y) y (F ⁻¹ᵁ V b) hb (ψ b) * e₂

theorem exists_nbhd (hN' : N'.IsLB) (hF : Topology.IsInducing F) (hs : Function.Surjective F)
    (x : X) : ∃ (U : X.Opens) (k' : N'.ι), x ∈ U ∧ F ⁻¹ᵁ U ≤ N'.U k' := by
  obtain ⟨y, rfl⟩ := hs x
  obtain ⟨k', hk'⟩ := exists_chart hN' y
  obtain ⟨U, hU, hle⟩ := exists_open hF hk'
  exact ⟨U, k', hU, hle⟩

end Iso

theorem exists_sec_lift : ∀ (A A₀ A' : Type) [CommRing A] [CommRing A₀] [CommRing A'] (g₀ : A →+* A₀) (g' : A →+* A') (a : A), Function.Surjective g₀ → Function.Surjective g' → IsNilpotent (RingHom.ker g₀) → RingHom.ker g' = Ideal.span {a} → a ∈ RingHom.ker g₀ → (∀ x, a * x = 0 ↔ x ∈ RingHom.ker g₀) → ∀ (X X₀ X' : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of A)) (f₀ : X₀ ⟶ Spec (CommRingCat.of A₀)) (f' : X' ⟶ Spec (CommRingCat.of A')) (j₀ : X₀ ⟶ X) (β : X' ⟶ X), Flat f → IsPullback j₀ f₀ f (Spec.map (CommRingCat.ofHom g₀)) → IsPullback β f' f (Spec.map (CommRingCat.ofHom g')) → ∀ (N : LB X) (N₀ : LB X₀) (w₀ : LB.Iso N₀ (N.pull j₀)), N.IsLB → N₀.IsLB → w₀.IsGen → FirstCohomologyVanishes N₀ → ∀ (N' : LB X') (w' : LB.Iso N' (N.pull β)), N'.IsLB → w'.IsGen → ∀ s' : LB.Sec N', ∃ s : LB.Sec N, (∀ z (k : (N).ι) (k' : (N').ι), (β) z ∈ (N).U k → z ∈ (N').U k' → gs (β) z _ ((s).f k) = (Geo.Tor.gw (w') (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s').f k')) := by
  intro A A₀ A' _ _ _ g₀ g' a hg₀ hg' hn hk' ha hann X X₀ X' f f₀ f' j β _ P₀ P' N N₀ w₀ hN hN₀ hw₀
    H N' w' hN' hw' s'
  have nil : ∀ x ∈ RingHom.ker g₀, IsNilpotent x := fun x hx => by
    obtain ⟨n, hn⟩ := hn
    exact ⟨n, by simpa [hn] using Ideal.pow_mem_pow hx n⟩
  have sj := surj_of_nil hg₀ nil P₀
  have sβ := surj_of_nil hg' (fun x hx => nil x (by
    rw [hk'] at hx
    exact (Ideal.span_singleton_le_iff_mem _).2 ha hx)) P'
  have hS := stalk_iff hg₀ hann P₀
  let I := {q : N.ι × N₀.ι × N'.ι × X.Opens // IsAffineOpen q.2.2.2 ∧ q.2.2.2 ≤ N.U q.1 ∧
    j ⁻¹ᵁ q.2.2.2 ≤ N₀.U q.2.1 ∧ β ⁻¹ᵁ q.2.2.2 ≤ N'.U q.2.2.1}
  obtain ⟨I, V, k, k₀, k', hV, h, h₀, h', cov⟩ : ∃ (I : Type) (V : I → X.Opens) (k : I → N.ι)
      (k₀ : I → N₀.ι) (k' : I → N'.ι), (∀ i, IsAffineOpen (V i)) ∧ (∀ i, V i ≤ N.U (k i)) ∧
      (∀ i, j ⁻¹ᵁ V i ≤ N₀.U (k₀ i)) ∧ (∀ i, β ⁻¹ᵁ V i ≤ N'.U (k' i)) ∧ ∀ x, ∃ i, x ∈ V i := by
    refine ⟨I, fun q => q.1.2.2.2, fun q => q.1.1, fun q => q.1.2.1, fun q => q.1.2.2.1,
      fun q => q.2.1, fun q => q.2.2.1, fun q => q.2.2.2.1, fun q => q.2.2.2.2, fun x => ?_⟩
    obtain ⟨k, hk⟩ := exists_chart hN x
    obtain ⟨U₀, k₀, m₀, l₀⟩ := exists_nbhd hN₀ (inducing_of_surj hg₀ P₀) sj x
    obtain ⟨U', k', m', l'⟩ := exists_nbhd hN' (inducing_of_surj hg' P') sβ x
    obtain ⟨V, hV, hx, hl⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
      (show x ∈ N.U k ⊓ U₀ ⊓ U' from ⟨⟨hk, m₀⟩, m'⟩)
    exact ⟨⟨(k, k₀, k', V), hV, fun _ hy => (hl hy).1.1, fun _ hy => l₀ (hl hy).1.2,
      fun _ hy => l' (hl hy).2⟩, hx⟩
  choose ω hω using fun i => exists_unit w' (k i) (k' i) (h i) (h' i)
  choose u hu using fun i => app_surj hg' P' (hV i) ((ω i).val * rs X' (h' i) (s'.f (k' i)))
  have hu' : ∀ i (z : X') (hz : β z ∈ V i), gr (𝟙 X' ≫ β) z (V i) hz (u i) =
      (Geo.Tor.gw w' (𝟙 X') z (k i) (k' i)).val * gr (𝟙 X') z _ (h' i hz) (s'.f (k' i)) :=
    fun i z hz => by rw [← gr_app (𝟙 X') β z (V i) hz, hu, map_mul, hω, gr_res]
  have key : ∀ (l : N.ι) (l' : N'.ι) i (z : X') (hl : β z ∈ N.U l) (hl' : z ∈ N'.U l')
      (hz : β z ∈ V i), gr (𝟙 X' ≫ β) z (N.U l ⊓ N.U (k i)) ⟨hl, h i hz⟩ (N.g l (k i)).val *
        gr (𝟙 X' ≫ β) z (V i) hz (u i) =
      (Geo.Tor.gw w' (𝟙 X') z l l').val * gr (𝟙 X') z _ hl' (s'.f l') := fun l l' i z hl hl' hz => by
    rw [hu', sec_rel s' z hl' (h' i hz), ← _root_.mul_assoc, ← _root_.mul_assoc,
      iso_rel hw' z hl (h i hz) hl' (h' i hz)]
  let d : ∀ i l, Γ(X, V i ⊓ V l) := fun i l => rs X inf_le_left (u i) -
    rs X (inf_le_inf (h i) (h l)) (N.g (k i) (k l)).val * rs X inf_le_right (u l)
  have hd : ∀ i l (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (hz : r z ∈ V i ⊓ V l),
      gr r z _ hz (d i l) = gr r z (V i) hz.1 (u i) -
        gr r z (N.U (k i) ⊓ N.U (k l)) ⟨h i hz.1, h l hz.2⟩ (N.g (k i) (k l)).val *
          gr r z (V l) hz.2 (u l) := fun i l Z r z hz => by
    simp only [d]
    rw [map_sub, map_mul, gr_res, gr_res, gr_res]
  choose φ hφ using fun i l => exists_div (a := a) (f := f) (j := j) (fun y e => (hS y e).1)
    (V i ⊓ V l) (d i l) (fun W hle hW => by
      have := mem_of_app_eq_zero hg' P' hW (rs X hle (d i l)) (gr_ext fun z hz => by
        rw [gr_app, gr_res, hd, map_zero, key (k i) (k' i) l z (h i (hle hz).1) (h' i (hle hz).1)
          (hle hz).2, hu' i z (hle hz).1, sub_self])
      rwa [hk', Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton] at this)
  obtain ⟨ψ, hψ⟩ := split_cocycle hw₀ H V cov k k₀ h h₀ φ (fun i l m y hi hl hm => by
    obtain ⟨e₁, p₁, q₁⟩ := hφ i l y ⟨hi, hl⟩
    obtain ⟨e₂, p₂, q₂⟩ := hφ l m y ⟨hl, hm⟩
    obtain ⟨e₃, p₃, q₃⟩ := hφ i m y ⟨hi, hm⟩
    rw [← q₁, ← q₂, ← q₃, ← stalkMap_gr, ← map_mul, ← map_add, ← sub_eq_zero, ← map_sub, ← hS]
    rw [hd] at p₁ p₂ p₃
    have c := gr_cocycle hN (𝟙 X) (j y) (h i hi) (h l hl) (h m hm)
    linear_combination p₃ - p₁ - gr (𝟙 X) (j y) (N.U (k i) ⊓ N.U (k l)) ⟨h i hi, h l hl⟩
      (N.g (k i) (k l)).val * p₂ - gr (𝟙 X) (j y) (V m) hm (u m) * c)
  choose v hv using fun i => app_surj hg₀ P₀ (hV i) (ψ i)
  obtain ⟨s, hs⟩ := sec_of_refine hN V cov k h (fun i => u i - cst f (V i) a * v i)
    (fun i l x hi hl => by
      obtain ⟨y, rfl⟩ := sj x
      obtain ⟨e, p, q⟩ := hφ i l y ⟨hi, hl⟩
      have c := hψ i l y hi hl
      rw [← q, ← hv, ← hv, gr_app, gr_app, ← stalkMap_gr, ← stalkMap_gr, ← stalkMap_gr, ← map_mul,
        ← map_sub, ← sub_eq_zero, ← map_sub, ← hS] at c
      rw [hd] at p
      rw [map_sub, map_sub, map_mul, map_mul, gr_cst, gr_cst]
      linear_combination p + c)
  refine ⟨s, fun z l l' hl hl' => ?_⟩
  obtain ⟨i, hi⟩ := cov (β z)
  have c := hs l i _ (𝟙 X' ≫ β) z hl hi
  have ha' : g' a = 0 := by
    rw [← RingHom.mem_ker, hk']
    exact Ideal.mem_span_singleton_self a
  rw [map_sub, map_mul, gr_cst, Category.assoc, P'.w, ← Category.assoc, cstS_comp, ha', map_zero,
    zero_mul, sub_zero, key l l' i z hl hl' hi] at c
  rw [gs_eq β z _ hl, gs_eq (𝟙 X') z _ hl']
  exact c

end GlobalTheory.SecLift
