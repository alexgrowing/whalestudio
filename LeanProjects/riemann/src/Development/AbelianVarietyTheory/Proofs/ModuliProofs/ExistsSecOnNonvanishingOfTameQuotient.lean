import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsQuasicoherentOfForallExistsAffine
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSumSmulSeparatingInertia
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsActionOfIsPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSmulApplyEqOfEqOnInvariants
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory.DescTheta

open GlobalTheory.LB

theorem exists_trace_ne_zero {Γ B A K : Type} [Group Γ] [Fintype Γ] [CommRing B] [CommRing A]
    [Field K] [MulSemiringAction Γ B] [MulSemiringAction Γ A] (f : B →+* A)
    (hf : ∀ (g : Γ) b, f (g • b) = g • f b) (ev : A →+* K)
    (hc : (Nat.card ((RingHom.ker (ev.comp f)).inertia Γ) : K) ≠ 0) (x : A)
    (hI : ∀ g ∈ (RingHom.ker (ev.comp f)).inertia Γ, ev (g • x) = ev x) (hx : ev x ≠ 0) :
    ∃ c : B, ev (∑ g : Γ, g • (f c * x)) ≠ 0 := by
  classical
  obtain ⟨n, c, d, s, hs, h⟩ := exists_sum_smul_separating_inertia Γ B _
    (RingHom.ker_isPrime (ev.comp f))
  by_contra! H
  have h1 : ∑ j, ev (f (d j)) * ev (∑ g : Γ, g • (f (c j) * x)) = 0 := by
    simp only [H, mul_zero, Finset.sum_const_zero]
  have h2 : ∑ j, ev (f (d j)) * ev (∑ g : Γ, g • (f (c j) * x)) =
      ∑ g : Γ, ev (f (∑ j, d j * g • c j)) * ev (g • x) := by
    simp only [map_sum, Finset.mul_sum, Finset.sum_mul, smul_mul', map_mul, hf, _root_.mul_assoc]
    rw [Finset.sum_comm]
  have h3 : ∀ g : Γ, ev (f (∑ j, d j * g • c j)) * ev (g • x) =
      if g ∈ (RingHom.ker (ev.comp f)).inertia Γ then ev (f s) * ev x else 0 := by
    intro g
    split_ifs with hg
    · have := (h g).1 hg
      rw [RingHom.mem_ker, map_sub, sub_eq_zero] at this
      rw [hI g hg]
      exact congrArg (· * ev x) this
    · have : ev (f (∑ j, d j * g • c j)) = 0 := (h g).2 hg
      rw [this, zero_mul]
  rw [h2] at h1
  simp only [h3] at h1
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, ← Fintype.card_subtype,
    ← Nat.card_eq_fintype_card] at h1
  exact mul_ne_zero hc (mul_ne_zero hs hx) h1

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

theorem nonvanishing_iso {L M : LB X} (hL : L.IsLB) (hM : M.IsLB) (w : LB.Iso L M) (hw : w.IsGen)
    {V : X.Opens} (s : Γ(toMod L, V)) (x : X) :
    (∃ p, x ∈ X.basicOpen (coord ((isoOfGen hL hM w hw).hom.app V s) p)) ↔
      ∃ q, x ∈ X.basicOpen (coord s q) := by
  have key (p : M.ι) (q : L.ι) (hp : x ∈ V ⊓ M.U p) (hq : x ∈ V ⊓ L.U q) :
      x ∈ X.basicOpen (coord ((isoOfGen hL hM w hw).hom.app V s) p) ↔
        x ∈ X.basicOpen (coord s q) := by
    have e := coord_isoOfGen_hom_app hL hM w hw s p q (W := (V ⊓ M.U p) ⊓ (V ⊓ L.U q))
      inf_le_left inf_le_right (inf_le_inf inf_le_right inf_le_right)
    have e' := congrArg (fun a => x ∈ X.basicOpen a) e
    simp only [mem_basicOpen_mul, mem_basicOpen_resG, eq_iff_iff] at e'
    have hx : x ∈ (V ⊓ M.U p) ⊓ (V ⊓ L.U q) := ⟨hp, hq⟩
    have hx' : x ∈ X.basicOpen (U := M.U p ⊓ L.U q)
        ((show Γ(X, M.U p ⊓ L.U q)ˣ from w.s (p, q)) : Γ(X, M.U p ⊓ L.U q)) :=
      (X.basicOpen_of_isUnit (U := M.U p ⊓ L.U q) (Units.isUnit _)).ge ⟨hp.2, hq.2⟩
    exact ⟨fun h => (e'.1 ⟨hx, h⟩).2.2, fun h => (e'.2 ⟨⟨hx, hx'⟩, hx, h⟩).2⟩
  constructor
  · rintro ⟨p, hp⟩
    have hp' := X.basicOpen_le _ hp
    obtain ⟨q, hq⟩ := TopologicalSpace.Opens.mem_iSup.1 (hL.cover.ge (Set.mem_univ x))
    exact ⟨q, (key p q hp' ⟨hp'.1, hq⟩).1 hp⟩
  · rintro ⟨q, hq⟩
    have hq' := X.basicOpen_le _ hq
    obtain ⟨p, hp⟩ := TopologicalSpace.Opens.mem_iSup.1 (hM.cover.ge (Set.mem_univ x))
    exact ⟨p, (key p q ⟨hq'.1, hp⟩ hq').2 hq⟩

theorem exists_nhds_nonvanishing {G : Over X} {L : LB G.left} (h : PushInvertible G L)
    {W : X.Opens} {O : G.left.Opens} (hO : G.hom ⁻¹ᵁ W ≤ O) (s : Γ(toMod L, O)) (u : G.left)
    (hu : G.hom u ∈ W) (hs : ∃ i, u ∈ G.left.basicOpen (coord s i)) :
    ∃ U : X.Opens, U ≤ W ∧ G.hom u ∈ U ∧ ∀ z ∈ U, ∃ u' : G.left, G.hom u' = z ∧
      ∃ i, u' ∈ G.left.basicOpen (coord s i) := by
  obtain ⟨V, hV, θ, -, h1, h2⟩ := h (G.hom u)
  have hle : G.hom ⁻¹ᵁ (W ⊓ V) ≤ O := (G.hom.preimage_mono inf_le_left).trans hO
  obtain ⟨a, ha, -⟩ := h1 (W ⊓ V) inf_le_right _
    (coord_mem ((toMod L).presheaf.map (homOfLE hle).op s))
  have key (i : L.ι) (u' : G.left) (h' : G.hom u' ∈ W ⊓ V) :
      u' ∈ G.left.basicOpen (coord s i) ↔
        G.hom u' ∈ X.basicOpen a ∧ u' ∈ G.left.basicOpen (θ i) := by
    have e' := congrArg (fun a => u' ∈ G.left.basicOpen a) (ha i)
    simp only [coord_map, mem_basicOpen_mul, mem_basicOpen_resG, mem_basicOpen_appLE,
      eq_iff_iff] at e'
    by_cases hi : u' ∈ L.U i
    · have hx : u' ∈ G.hom ⁻¹ᵁ (W ⊓ V) ⊓ L.U i := ⟨h', hi⟩
      simpa only [hx, true_and] using e'
    · exact ⟨fun h => (hi (G.left.basicOpen_le _ h).2).elim,
        fun h => (hi (G.left.basicOpen_le _ h.2).2).elim⟩
  obtain ⟨i, hi⟩ := hs
  refine ⟨X.basicOpen a, (X.basicOpen_le a).trans inf_le_left, ((key i u ⟨hu, hV⟩).1 hi).1,
    fun z hz => ?_⟩
  obtain ⟨u', j, rfl, hj⟩ := h2 z (X.basicOpen_le a hz).2
  exact ⟨u', rfl, j, (key j u' (X.basicOpen_le a hz)).2 ⟨hz, hj⟩⟩

theorem isQuasicoherent_pushforward {G : Over X} {L : LB G.left} (h : PushInvertible G L) :
    ((Scheme.Modules.pushforward G.hom).obj (toMod L)).IsQuasicoherent := by
  choose V hV θ hθ h1 h2 using h
  refine QCoh.isQuasicoherent_of_restrict _ (fun x => (V x).ι) (fun x => ⟨x, ?_⟩) fun x => ?_
  · rw [Scheme.Opens.opensRange_ι]; exact hV x
  · have e := Descent.freeIso (F := (Scheme.Modules.pushforward G.hom).obj (toMod L))
      (s := mkSec (θ x) (hθ x)) (Descent.bijective_smul_stalk fun W hW => by
        refine (Function.bijective_iff_existsUnique _).2 fun (s : Γ(toMod L, G.hom ⁻¹ᵁ W)) => ?_
        refine (existsUnique_congr fun a => ?_).1 (h1 x W hW _ (coord_mem s))
        refine ⟨fun h => sec_ext (L := L) fun i => (h i).symm, fun h i => ?_⟩
        exact (congrArg (fun t => coord (L := L) t i) h).symm)
    exact (SheafOfModules.isQuasicoherent (V x).toScheme.ringCatSheaf).prop_of_iso ((trivIso _).symm ≪≫ e)
      (isQuasicoherent_toMod (Out.Inh.trivLB_isLB _))

theorem exists_sec_nonvanishing {G : Over X} {L : LB G.left} (h : PushInvertible G L)
    {W : X.Opens} (hW : IsAffineOpen W) {x : X} (hx : x ∈ W) :
    ∃ (s : Γ(toMod L, G.hom ⁻¹ᵁ W)) (u : G.left), G.hom u = x ∧
      ∃ i, u ∈ G.left.basicOpen (coord s i) := by
  have := isQuasicoherent_pushforward h
  obtain ⟨V, hV, θ, hθ, -, h2⟩ := h x
  obtain ⟨b, hb, hxb⟩ := hW.exists_basicOpen_le ⟨x, hV⟩ hx
  obtain ⟨n, t, ht⟩ := QCoh.exists_pow_smul_eq_res ((Scheme.Modules.pushforward G.hom).obj (toMod L))
    hW b (X.basicOpen_le b) rfl
    ((toMod L).presheaf.map (homOfLE (G.hom.preimage_mono hb)).op (mkSec θ hθ))
  obtain ⟨u, i, rfl, hi⟩ := h2 x hV
  refine ⟨t, u, rfl, i, ?_⟩
  have e : (G.hom.appLE (X.basicOpen b) (G.hom ⁻¹ᵁ (X.basicOpen b) ⊓ L.U i) inf_le_left).hom
      (resG X (X.basicOpen_le b) b ^ n) *
        resG G.left (inf_le_inf_right _ (G.hom.preimage_mono hb)) (θ i) =
      resG G.left (inf_le_inf_right _ (G.hom.preimage_mono (X.basicOpen_le b)))
        (coord (L := L) t i) := congrArg (fun t => coord (L := L) t i) ht
  have e' := congrArg (fun a => u ∈ G.left.basicOpen a) e
  simp only [mem_basicOpen_mul, mem_basicOpen_resG, mem_basicOpen_appLE, eq_iff_iff] at e'
  have hu : u ∈ G.hom ⁻¹ᵁ (X.basicOpen b) ⊓ L.U i := ⟨hxb, (G.left.basicOpen_le _ hi).2⟩
  refine (e'.1 ⟨⟨hu, ?_⟩, hu, hi⟩).2
  have hb' : IsUnit (resG X (X.basicOpen_le b) b) := X.toRingedSpace.isUnit_res_basicOpen b
  rw [X.basicOpen_of_isUnit (hb'.pow n)]
  exact hxb

theorem le_pull_chart {L : LB X} (φ : Y ⟶ X) (O : X.Opens) (i : L.ι) :
    φ ⁻¹ᵁ (O ⊓ L.U i) ≤ φ ⁻¹ᵁ O ⊓ (L.pull φ).U (fun _ => i) :=
  le_inf (φ.preimage_mono inf_le_left)
    ((φ.preimage_mono inf_le_right).trans (pull_U φ (fun _ => i)).ge)

theorem exists_descent {Γ : Type} [Group Γ] [Fintype Γ] {Y' : Scheme.{0}} (τ : Γ →* Aut Y)
    (φ : Y ⟶ Y') (hφ : ∀ g, (τ g).hom ≫ φ = φ)
    (hq : ∀ V : Y'.Opens, Function.Injective (φ.app V).hom ∧ ∀ f : Γ(Y, φ ⁻¹ᵁ V),
      (∀ g (h : φ ⁻¹ᵁ V ≤ (τ g).hom ⁻¹ᵁ (φ ⁻¹ᵁ V)), ((τ g).hom.appLE _ _ h).hom f = f) →
        f ∈ Set.range (φ.app V).hom)
    {L : LB Y'} (O : Y'.Opens) (s : Γ(toMod (L.pull φ), φ ⁻¹ᵁ O)) :
    ∃ t : Γ(toMod L, O), ∀ i, (φ.app (O ⊓ L.U i)).hom (coord t i) =
      ∑ g : Γ, ((τ g⁻¹).hom.appLE _ _ (preimage_le_of_invariant τ φ hφ _ _)).hom
        (resG Y (le_pull_chart φ O i :
          φ ⁻¹ᵁ (O ⊓ L.U i) ≤ φ ⁻¹ᵁ O ⊓ (L.pull φ).U (fun _ => i)) (coord s (fun _ => i))) := by
  have H (i : L.ι) (u : Γ(Y, φ ⁻¹ᵁ (O ⊓ L.U i))) :
      (∑ g : Γ, ((τ g⁻¹).hom.appLE _ _ (preimage_le_of_invariant τ φ hφ _ _)).hom u) ∈
        Set.range (φ.app (O ⊓ L.U i)).hom := by
    refine (hq _).2 _ fun k _ => ?_
    let := sectionsAction τ _ (preimage_le_of_invariant τ φ hφ (O ⊓ L.U i))
    have e : k⁻¹ • ∑ g : Γ, g • u = ∑ g : Γ, g • u := by
      rw [Finset.smul_sum]
      simp only [← mul_smul]
      exact Equiv.sum_comp (Equiv.mulLeft k⁻¹) (fun g => g • u)
    have e' : ((τ k⁻¹⁻¹).hom.appLE _ _ (preimage_le_of_invariant τ φ hφ _ _)).hom
      (∑ g : Γ, g • u) = ∑ g : Γ, g • u := e
    simp only [inv_inv] at e'
    exact e'
  choose t ht using fun i => H i (resG Y (le_pull_chart φ O i :
          φ ⁻¹ᵁ (O ⊓ L.U i) ≤ φ ⁻¹ᵁ O ⊓ (L.pull φ).U (fun _ => i)) (coord s (fun _ => i)))
  refine ⟨mkSec t fun i j => ((hq _).1 ?_), ht⟩
  have l (i : L.ι) : φ ⁻¹ᵁ (O ⊓ L.U i) ≤ φ ⁻¹ᵁ O ⊓ (L.pull φ).U (fun _ => i) :=
    le_pull_chart φ O i
  have li : O ⊓ L.U i ⊓ L.U j ≤ O ⊓ L.U i := inf_le_left
  have lj : O ⊓ L.U i ⊓ L.U j ≤ O ⊓ L.U j := inf_le_inf_right _ inf_le_left
  have key (k : L.ι) (lk : O ⊓ L.U i ⊓ L.U j ≤ O ⊓ L.U k) :
      (φ.app _).hom (resG Y' lk (t k)) = ∑ g : Γ,
        ((τ g⁻¹).hom.appLE _ _ (preimage_le_of_invariant τ φ hφ (O ⊓ L.U i ⊓ L.U j) _)).hom
          (resG Y ((φ.preimage_mono lk).trans (l k)) (coord s (fun _ => k))) := by
    rw [Scheme.Hom.app_eq_appLE, appLE_resG, ← resG_app, ht k, map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [resG_appLE, appLE_resG, appLE_resG]
  rw [map_mul, key i li, key j lj, Finset.mul_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [coord_rel s (fun _ => i) (fun _ => j) _ ((φ.preimage_mono lj).trans (l j))
    (le_inf (((φ.preimage_mono li).trans (l i)).trans inf_le_right)
      (((φ.preimage_mono lj).trans (l j)).trans inf_le_right)), map_mul,
    resG_pull_g φ (L := L) (fun _ => i) (fun _ => j)]
  congr 1
  rw [Scheme.Hom.app_eq_appLE, appLE_resG, ← RingHom.comp_apply, ← CommRingCat.hom_comp]
  simp only [Scheme.Hom.appLE_comp_appLE, hφ]

noncomputable def evalAt {k : Type} [Field k] (ζ : Sp k ⟶ X) (U : X.Opens) (h : ⊤ ≤ ζ ⁻¹ᵁ U) :
    Γ(X, U) →+* k :=
  (ζ.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (.of k)).hom).hom

theorem evalAt_ne_zero {k : Type} [Field k] (ζ : Sp k ⟶ X) (U : X.Opens) (h : ⊤ ≤ ζ ⁻¹ᵁ U)
    (a : Γ(X, U)) (z : Sp k) : evalAt ζ U h a ≠ 0 ↔ ζ z ∈ X.basicOpen a := by
  have e := mem_basicOpen_appLE ζ h a z
  rw [basicOpen_eq_of_affine'] at e
  have hz : z.asIdeal = ⊥ := @Ideal.eq_bot_of_prime k _ z.asIdeal z.isPrime
  have e2 : z ∈ PrimeSpectrum.basicOpen (evalAt ζ U h a) ↔ evalAt ζ U h a ≠ 0 := by
    change evalAt ζ U h a ∉ z.asIdeal ↔ _
    rw [hz, Ideal.mem_bot]
  rw [← e2]
  exact e.trans (and_iff_right trivial)

theorem evalAt_appLE {k : Type} [Field k] (ζ : Sp k ⟶ Y) (f : Y ⟶ X) (U : X.Opens) (V : Y.Opens)
    (h : ⊤ ≤ ζ ⁻¹ᵁ V) (e : V ≤ f ⁻¹ᵁ U) (a : Γ(X, U)) (ξ : Sp k ⟶ X) (hξ : ζ ≫ f = ξ)
    (h' : ⊤ ≤ ξ ⁻¹ᵁ U) :
    evalAt ζ V h ((f.appLE U V e).hom a) = evalAt ξ U h' a := by
  subst hξ
  simp only [evalAt, ← Scheme.Hom.appLE_comp_appLE ζ f U V ⊤ e h, CommRingCat.hom_comp,
    RingHom.comp_apply]

theorem mem_inertia_iff {Γ k : Type} [Group Γ] [Field k] (ρ : Γ →* Aut X) {W : X.Opens}
    (hW : IsAffineOpen W) (hst : ∀ g, W ≤ (ρ g).hom ⁻¹ᵁ W) (ξ : Sp k ⟶ X) (h : ⊤ ≤ ξ ⁻¹ᵁ W)
    (g : Γ) :
    letI := sectionsAction ρ W hst
    g⁻¹ ∈ (RingHom.ker (evalAt ξ W h)).inertia Γ ↔ ξ ≫ (ρ g).hom = ξ := by
  let := sectionsAction ρ W hst
  have e (b : Γ(X, W)) : g⁻¹ • b = ((ρ g).hom.appLE W W (hst g)).hom b := by
    have : g⁻¹ • b = ((ρ g⁻¹⁻¹).hom.appLE W W (hst _)).hom b := rfl
    simpa only [inv_inv] using this
  refine ⟨fun hg => ?_, fun hg b => ?_⟩
  · have e1 : ξ.appLE _ ⊤ h = (ρ g).hom.appLE _ _ (hst _) ≫ ξ.appLE _ ⊤ h := by
      rw [← cancel_mono (Scheme.ΓSpecIso (.of k)).hom]
      ext b
      have : evalAt ξ W h (g⁻¹ • b - b) = 0 := hg b
      rw [map_sub, sub_eq_zero, e] at this
      exact this.symm
    have hT := isAffineOpen_top (Sp k)
    have : IsIso hT.fromSpec := by rw [IsAffineOpen.fromSpec_top]; infer_instance
    symm
    rw [← cancel_epi hT.fromSpec, ← IsAffineOpen.SpecMap_appLE_fromSpec ξ hW hT h, e1,
      Spec.map_comp, Category.assoc, IsAffineOpen.SpecMap_appLE_fromSpec _ hW hW,
      IsAffineOpen.SpecMap_appLE_fromSpec_assoc ξ hW hT h]
  · change evalAt ξ W h (g⁻¹ • b - b) = 0
    rw [map_sub, sub_eq_zero, e]
    exact evalAt_appLE ξ _ _ _ _ _ b ξ hg h

theorem nonvanishing_pullSec {L : LB X} (φ : Y ⟶ X) {O : X.Opens} (t : Γ(toMod L, O)) (y : Y) :
    (∃ j, y ∈ Y.basicOpen (coord (pullSec L φ O t) j)) ↔ ∃ i, φ y ∈ X.basicOpen (coord t i) := by
  simp only [coord_pullSec, mem_basicOpen_appLE]
  exact ⟨fun ⟨j, hj⟩ => ⟨_, hj.2⟩,
    fun ⟨i, hi⟩ => ⟨fun _ => i, le_pull_chart φ O i (X.basicOpen_le _ hi), hi⟩⟩

theorem exists_descent_nonvanishing {Γ : Type} [Group Γ] [Finite Γ] {X' G G' : Scheme.{0}}
    (ρ : Γ →* Aut X) (π : X ⟶ X') (p : G ⟶ X) (p' : G' ⟶ X') (φ : G ⟶ G') (τ : Γ →* Aut G)
    (hπ : ∀ g, (ρ g).hom ≫ π = π) (w : φ ≫ p' = p ≫ π) (hφ : ∀ g, (τ g).hom ≫ φ = φ)
    (hp : ∀ g, (τ g).hom ≫ p = p ≫ (ρ g).hom)
    (hq : ∀ V : G'.Opens, Function.Injective (φ.app V).hom ∧ ∀ f : Γ(G, φ ⁻¹ᵁ V),
      (∀ g (h : φ ⁻¹ᵁ V ≤ (τ g).hom ⁻¹ᵁ (φ ⁻¹ᵁ V)), ((τ g).hom.appLE _ _ h).hom f = f) →
        f ∈ Set.range (φ.app V).hom)
    (htame : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X),
      (Nat.card {g // x ≫ (ρ g).hom = x} : k) ≠ 0)
    (hfib : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X) g, x ≫ (ρ g).hom = x →
      pullback.fst p x ≫ (τ g).hom = pullback.fst p x)
    {L : LB G'} {V : X'.Opens} (hW : IsAffineOpen (π ⁻¹ᵁ V))
    (s : Γ(toMod (L.pull φ), φ ⁻¹ᵁ p' ⁻¹ᵁ V)) (u : G) (hs : ∃ j, u ∈ G.basicOpen (coord s j)) :
    ∃ (t : Γ(toMod L, p' ⁻¹ᵁ V)) (i : L.ι), φ u ∈ G'.basicOpen (coord t i) := by
  have := Fintype.ofFinite Γ
  obtain ⟨j, hj⟩ := hs
  obtain ⟨i, rfl⟩ : ∃ i : L.ι, j = fun _ => i := ⟨j PUnit.unit, rfl⟩
  have hu : u ∈ φ ⁻¹ᵁ (p' ⁻¹ᵁ V ⊓ L.U i) := pull_inf_le φ _ _ (G.basicOpen_le _ hj)
  let k := AlgebraicClosure (G.residueField u)
  let ζ : Sp k ⟶ G := Spec.map (CommRingCat.ofHom (algebraMap (G.residueField u) k)) ≫
    G.fromSpecResidueField u
  have hζ (z : Sp k) : ζ z = u :=
    (Scheme.Hom.comp_apply _ _ z).trans (Scheme.fromSpecResidueField_apply _ _)
  have e : φ ⁻¹ᵁ p' ⁻¹ᵁ V = p ⁻¹ᵁ π ⁻¹ᵁ V := by
    rw [← Scheme.Hom.comp_preimage, w, Scheme.Hom.comp_preimage]
  have hA : φ ⁻¹ᵁ (p' ⁻¹ᵁ V ⊓ L.U i) ≤ p ⁻¹ᵁ π ⁻¹ᵁ V :=
    (φ.preimage_mono inf_le_left).trans e.le
  have h1 : ⊤ ≤ ζ ⁻¹ᵁ φ ⁻¹ᵁ (p' ⁻¹ᵁ V ⊓ L.U i) := fun z _ => by
    change ζ z ∈ φ ⁻¹ᵁ (p' ⁻¹ᵁ V ⊓ L.U i)
    rwa [hζ]
  have h2 : ⊤ ≤ (ζ ≫ p) ⁻¹ᵁ π ⁻¹ᵁ V := h1.trans (ζ.preimage_mono hA)
  have hst := preimage_le_of_invariant ρ π hπ V
  have hst' := preimage_le_of_invariant τ φ hφ (p' ⁻¹ᵁ V ⊓ L.U i)
  let := sectionsAction ρ _ hst
  let := sectionsAction τ _ hst'
  have hev : (evalAt ζ _ h1).comp (p.appLE _ _ hA).hom = evalAt (ζ ≫ p) _ h2 :=
    RingHom.ext fun b => evalAt_appLE ζ p _ _ h1 hA b _ rfl h2
  have hI (g : Γ) := mem_inertia_iff ρ hW hst (ζ ≫ p) h2 g
  let z : Sp k := default
  obtain ⟨c, hc⟩ := exists_trace_ne_zero (Γ := Γ) (p.appLE _ _ hA).hom (fun g b => by
      change (p.appLE _ _ hA).hom (((ρ g⁻¹).hom.appLE _ _ (hst _)).hom b) =
        ((τ g⁻¹).hom.appLE _ _ (hst' _)).hom ((p.appLE _ _ hA).hom b)
      simp only [← RingHom.comp_apply, ← CommRingCat.hom_comp, Scheme.Hom.appLE_comp_appLE, hp])
    (evalAt ζ _ h1) (by
      rw [hev]
      convert htame k (ζ ≫ p) using 2
      exact Nat.card_congr (Equiv.subtypeEquivRight fun g => by rw [← hI, inv_mem_iff]))
    (resG G (le_pull_chart φ _ i) (coord s fun _ => i)) (fun g hg => by
      rw [hev, ← inv_inv g, hI] at hg
      have := pullback.lift ζ (𝟙 _) (Category.id_comp _).symm ≫= hfib k (ζ ≫ p) _ hg
      rw [pullback.lift_fst_assoc, pullback.lift_fst] at this
      exact evalAt_appLE ζ (τ g⁻¹).hom _ _ h1 (hst' _) _ ζ this h1)
    (by
      rw [evalAt_ne_zero _ _ _ _ z, hζ, mem_basicOpen_resG]
      exact ⟨hu, hj⟩)
  obtain ⟨t, ht⟩ := exists_descent τ φ hφ hq _ ((p.appLE _ _ e.le).hom c • s)
  refine ⟨t, i, ?_⟩
  rw [evalAt_ne_zero _ _ _ _ z, hζ] at hc
  have h3 := ht i
  rw [coord_smul (L := L.pull φ) _ s (fun _ => i), map_mul, resG_resG, resG_appLE, Scheme.Hom.app_eq_appLE] at h3
  refine ((mem_basicOpen_appLE φ le_rfl (coord t i) u).1 ?_).2
  rw [h3]
  exact hc

end GlobalTheory.DescTheta

namespace GlobalTheory

open DescTheta GlobalTheory.LB

theorem exists_secOn_nonvanishing_of_tame_quotient :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (X X' : Scheme.{0}) (ρ : Γ →* Aut X) (π : X ⟶ X') (G : Over X) (G' : Over X') (φ : G.left ⟶ G'.left) (τ : Γ →* Aut G.left) (L : LB G.left) (L' : LB G'.left), (IsAffineHom π ∧ (∀ g, (ρ g).hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → IsPullback φ G.hom G'.hom π → Flat G'.hom → (∀ g, (τ g).hom ≫ φ = φ ∧ (τ g).hom ≫ G.hom = G.hom ≫ (ρ g).hom) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X), (Nat.card {g // x ≫ (ρ g).hom = x} : k) ≠ 0) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X) g, x ≫ (ρ g).hom = x → pullback.fst G.hom x ≫ (τ g).hom = pullback.fst G.hom x) → L.IsLB → L'.IsLB → LBIso L (L'.pull φ) → PushInvertible G L → (∀ x : X', ∃ V : X'.Opens, x ∈ V ∧ ∃ θ ∈ secOn L' (G'.hom ⁻¹ᵁ V), ∀ y ∈ V, ∃ (g : G'.left) (i : L'.ι), G'.hom g = y ∧ g ∈ G'.left.basicOpen (θ i)) := by
  intro Γ _ _ X X' ρ π G G' φ τ L L' hQ H hflat hτ htame hfib hL hL' ⟨w, hw⟩ hP x'
  obtain ⟨-, hφ, hq⟩ := (quotient_flat_baseChange Γ X X' _ _ ρ π φ G.hom G'.hom hQ H hflat).2 τ hτ
  obtain ⟨-, hsurj, -, -, hopen⟩ := quotient_isIntegral_surjective_orbits Γ X X' ρ π hQ
  obtain ⟨_, hπ, -⟩ := hQ
  have hM := Semi.LB.isLB_pull hL' φ
  obtain ⟨_, ⟨V, hV, rfl⟩, hx, -⟩ :=
    X'.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x') isOpen_univ
  have hW : IsAffineOpen (π ⁻¹ᵁ V) := IsAffineOpen.preimage hV π
  obtain ⟨x, rfl⟩ := π.surjective x'
  have e : φ ⁻¹ᵁ G'.hom ⁻¹ᵁ V = G.hom ⁻¹ᵁ π ⁻¹ᵁ V := by
    rw [← Scheme.Hom.comp_preimage, H.w, Scheme.Hom.comp_preimage]
  obtain ⟨s, u, rfl, i, hi⟩ := exists_sec_nonvanishing hP hW hx
  obtain ⟨t, ht⟩ := exists_descent_nonvanishing ρ π G.hom G'.hom φ τ hπ H.w hφ (fun g => (hτ g).2)
    hq htame hfib hW ((isoOfGen hL hM w hw).hom.app _ ((toMod L).presheaf.map (homOfLE e.le).op s))
    u ((nonvanishing_iso hL hM w hw _ u).2 ⟨i, by
      rw [coord_map, mem_basicOpen_resG]
      exact ⟨⟨e.ge hx, (G.left.basicOpen_le _ hi).2⟩, hi⟩⟩)
  obtain ⟨s', hs'⟩ := (ConcreteCategory.bijective_of_isIso
    ((isoOfGen hL hM w hw).hom.app (φ ⁻¹ᵁ G'.hom ⁻¹ᵁ V))).2 (pullSec L' φ _ t)
  have key (y : G.left) : (∃ i, y ∈ G.left.basicOpen (coord s' i)) ↔
      ∃ i, φ y ∈ G'.left.basicOpen (coord t i) := by
    rw [← nonvanishing_iso hL hM w hw, hs', nonvanishing_pullSec]
  obtain ⟨U, -, hxU, hU⟩ := exists_nhds_nonvanishing hP e.ge s' u hx ((key u).2 ht)
  obtain ⟨V', hV'⟩ := hopen (⨆ g, (ρ g).hom ⁻¹ᵁ U) fun g => by
    have (h : Γ) : (ρ g).hom ⁻¹ᵁ (ρ h).hom ⁻¹ᵁ U = (ρ (h * g)).hom ⁻¹ᵁ U := by
      rw [map_mul]; rfl
    simp only [Scheme.Hom.preimage_iSup, this]
    exact Equiv.iSup_comp (g := fun h => (ρ h).hom ⁻¹ᵁ U) (Equiv.mulRight g)
  have hle : G'.hom ⁻¹ᵁ (V ⊓ V') ≤ G'.hom ⁻¹ᵁ V := G'.hom.preimage_mono inf_le_left
  refine ⟨V ⊓ V', ⟨hx, hV'.ge (TopologicalSpace.Opens.mem_iSup.2 ⟨1, ?_⟩)⟩, _,
    coord_mem ((toMod L').presheaf.map (homOfLE hle).op t), fun y hy => ?_⟩
  · rw [map_one]; exact hxU
  obtain ⟨z, rfl⟩ := π.surjective y
  obtain ⟨g, hg⟩ := TopologicalSpace.Opens.mem_iSup.1 (hV'.le hy.2)
  obtain ⟨v, hv, hv'⟩ := hU _ hg
  obtain ⟨j, hj⟩ := (key v).1 hv'
  have e2 : G'.hom (φ v) = π z := by
    rw [← Scheme.Hom.comp_apply, H.w, Scheme.Hom.comp_apply, hv, ← Scheme.Hom.comp_apply, hπ]
  refine ⟨φ v, j, e2, ?_⟩
  rw [coord_map, mem_basicOpen_resG]
  exact ⟨⟨by rw [← e2] at hy; exact hy, (G'.left.basicOpen_le _ hj).2⟩, hj⟩

end GlobalTheory
