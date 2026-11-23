import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopologicalKrullDimEqSucc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CechPic
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LineNorm GlobalTheory.TrueGeo.SmallSec

namespace GlobalTheory.InvertIdeal

section General

variable {X : Scheme.{0}} [IsIntegral X]

theorem exists_mul_pow {U : X.Opens} (hU : IsAffineOpen U) (h : genericPoint X ∈ U) (α : Γ(X, U))
    (hα : genericPoint X ∈ X.basicOpen α) {f : X.functionField} (hf : ∀ x ∈ X.basicOpen α, RegAt x f) :
    ∃ (n : ℕ) (γ : Γ(X, U)), fnOf U h γ = f * fnOf U h α ^ n := by
  obtain ⟨β, rfl⟩ := exists_fnOf_eq hα hf
  have := hU.isLocalization_basicOpen α
  obtain ⟨n, γ, e⟩ := IsLocalization.Away.surj α β
  refine ⟨n, γ, ?_⟩
  have e' := congrArg (fnOf _ hα) e
  rw [map_mul, map_pow] at e'
  have r (a : Γ(X, U)) : fnOf _ hα (algebraMap _ Γ(X, X.basicOpen α) a) = fnOf U h a :=
    fnOf_resG (X.basicOpen_le α) hα a
  rw [r, r] at e'
  exact e'.symm

theorem exists_denom {U : X.Opens} (hU : IsAffineOpen U) (h : genericPoint X ∈ U) {x : X} (hx : x ∈ U)
    {f : X.functionField} (hf : RegAt x f) :
    ∃ β γ : Γ(X, U), x ∈ X.basicOpen β ∧ fnOf U h γ = f * fnOf U h β := by
  obtain ⟨W, hW, a, rfl⟩ := hf.exists_fnOf
  obtain ⟨α, hle, hα⟩ := hU.exists_basicOpen_le (V := W) ⟨x, hW⟩ hx
  obtain ⟨n, γ, e⟩ := exists_mul_pow hU h α (gen_mem hα) fun y hy => regAt_fnOf (hle hy) (gen_mem hW) a
  refine ⟨α ^ (n + 1), γ * α, by rwa [X.basicOpen_pow α n.succ_pos], ?_⟩
  rw [map_mul, e, map_pow, pow_succ, mul_assoc]

omit [IsIntegral X] in

theorem mem_basicOpen_algX {O : Type} [CommRing O] (p : X ⟶ Sp O) (U : X.Opens) (a : O) (x : X) :
    x ∈ X.basicOpen (algX p U a) ↔ x ∈ U ∧ a ∉ (p x).asIdeal := by
  have e := Scheme.basicOpen_appLE p U ⊤ le_top ((Scheme.ΓSpecIso (CommRingCat.of O)).inv a)
  rw [basicOpen_eq_of_affine] at e
  exact SetLike.ext_iff.1 e x

theorem exists_comb {O : Type} [CommRing O] [IsDomain O] (p : X ⟶ Sp O) {U : X.Opens} (hU : IsAffineOpen U)
    (h : genericPoint X ∈ U) {ι : Type} [Fintype ι] (s : ι → X.functionField) (f : X.functionField)
    (hf : ∀ x ∈ U, (p x).asIdeal = ⊥ → ∃ i g, RegAt x g ∧ f = g * s i) :
    ∃ a : O, a ≠ 0 ∧ ∃ c : ι → Γ(X, U), fnOf U h (algX p U a) * f = ∑ i, fnOf U h (c i) * s i := by
  classical
  let J : Ideal Γ(X, U) :=
    { carrier := {β | ∃ c : ι → Γ(X, U), fnOf U h β * f = ∑ i, fnOf U h (c i) * s i}
      zero_mem' := ⟨0, by simp⟩
      add_mem' := fun ⟨c, hc⟩ ⟨c', hc'⟩ => ⟨c + c', by
        simp only [map_add, add_mul, hc, hc', Pi.add_apply, Finset.sum_add_distrib]⟩
      smul_mem' := fun a β ⟨c, hc⟩ => ⟨a • c, by
        simp only [smul_eq_mul, map_mul, mul_assoc, hc, Pi.smul_apply, Finset.mul_sum]⟩ }
  by_contra H
  obtain ⟨P, hP, hJ, hd⟩ := J.exists_le_prime_disjoint ((nonZeroDivisors O).map (algX p U))
    (Set.disjoint_left.2 fun β hβ ⟨a, ha, e⟩ => H ⟨a, nonZeroDivisors.ne_zero ha, e ▸ hβ⟩)
  let x : X := hU.fromSpec ⟨P, hP⟩
  have hx : x ∈ U := hU.range_fromSpec.le ⟨_, rfl⟩
  have hb (β : Γ(X, U)) : x ∈ X.basicOpen β ↔ β ∉ P := SetLike.ext_iff.1 (hU.fromSpec_preimage_basicOpen β) ⟨P, hP⟩
  obtain ⟨i, g, hg, e⟩ := hf x hx (eq_bot_iff.2 fun a ha => by
    by_contra h0
    exact ((mem_basicOpen_algX p U a x).1 ((hb _).2 fun h' =>
      Set.disjoint_left.1 hd h' ⟨a, mem_nonZeroDivisors_of_ne_zero h0, rfl⟩)).2 ha)
  obtain ⟨β, γ, hβ, e'⟩ := exists_denom hU h hx hg
  refine (hb β).1 hβ (hJ ⟨Pi.single i γ, ?_⟩)
  rw [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, map_zero, zero_mul]) (by simp),
    Pi.single_eq_same, e', e]
  ring

theorem eventually_regularAt [CompactSpace X] {A : CartierDiv X} (hA : A.Eff) (E : CartierDiv X) {f : X.functionField}
    (hf : ∀ x, A.GeneratesAt x 1 → E.RegularAt x f) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ x, (E + N • A).RegularAt x f := by
  have key (x : X) : ∃ U : X.Opens, x ∈ U ∧ ∀ᶠ N : ℕ in Filter.atTop, ∀ y ∈ U, (E + N • A).RegularAt y f := by
    obtain ⟨U₁, h₁, a, ha⟩ := A.exists_isEqn_nhds x
    obtain ⟨U₂, h₂, g, hg⟩ := E.exists_isEqn_nhds x
    obtain ⟨U, hU, hx, hle⟩ := exists_isAffineOpen_mem_and_subset (memInf h₁ h₂)
    obtain ⟨α, hα⟩ := exists_fnOf_eq (gen_mem hx) fun y hy => CartierDiv.eff_iff.1 hA y a (ha y (hle hy).1)
    have hu {y : X} (hy : y ∈ U) : UnitAt y (a : X.functionField) ↔ y ∈ X.basicOpen α := by
      rw [← hα, unitAt_fnOf_iff hy]
    obtain ⟨n, γ, e⟩ := exists_mul_pow hU (gen_mem hx) α ((hu (gen_mem hx)).1 (unitAt_genericPoint a.ne_zero))
      (f := f * g) fun y hy => by
        have hy' := X.basicOpen_le α hy
        exact (hg y (hle hy').2).regularAt_iff.1 (hf y ⟨a, ha y (hle hy').1, by rw [one_mul]; exact (hu hy').2 hy⟩)
    refine ⟨U, hx, Filter.eventually_atTop.2 ⟨n, fun N hN y hy => ?_⟩⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
    refine ⟨_, (hg y (hle hy).2).add ((ha y (hle hy).1).nsmul _), ?_⟩
    have := regAt_fnOf hy (gen_mem hx) (γ * α ^ k)
    rw [map_mul, map_pow, e, hα] at this
    convert this using 1
    push_cast
    ring
  choose U hU h using key
  obtain ⟨T, hT⟩ := exists_finset_iSup_eq_top U hU
  filter_upwards [Filter.eventually_all.2 fun x : T => h x] with N hN y
  obtain ⟨x, hx⟩ := Opens.mem_iSup.1 (hT.ge (Set.mem_univ y))
  exact hN x y hx

theorem exists_div_sec {L : LB X} (hL : L.IsLB) (σ : L.Sec) (hσ : genericPoint X ∈ nonzeroLocus σ) :
    ∃ A : CartierDiv X, A.Eff ∧ toPic A = cls L hL ∧ ∀ x, A.GeneratesAt x 1 ↔ x ∈ nonzeroLocus σ := by
  obtain ⟨i, hi⟩ := exists_chart hL (genericPoint X)
  have P := presents_ofLB hL i hi
  let g : X.functionFieldˣ := Units.mk0 _ ((P.generatesAt_rat_iff σ).2 hσ).ne_zero
  refine ⟨_ + CartierDiv.principal g, fun x => CartierDiv.regularAt_add_principal.2 ?_, (P.add_principal g).toPic_eq,
    fun x => ?_⟩
  · rw [one_mul]
    exact CartierDiv.mem_sections.1 (P.rat_mem σ) x
  · obtain ⟨g', h⟩ := (ofLB hL i hi).exists_isEqn x
    rw [← P.generatesAt_rat_iff, (h.add (CartierDiv.isEqn_principal g x)).generatesAt_iff, h.generatesAt_iff, one_mul,
      Units.val_mul, mul_comm]
    rfl

theorem eventually_generates {R : Type} [CommRing R] (q : X ⟶ Sp R) [IsProper q] {L : LB X} (hL : IsAmpleLB L)
    {A : CartierDiv X} (hA : toPic A = cls L hL.isLB) (E : CartierDiv X) :
    ∀ᶠ N : ℕ in Filter.atTop, ∃ (m : ℕ) (w : Fin m → X.functionField), (∀ a x, (E + N • A).RegularAt x (w a)) ∧
      ∀ x, ∃ a, (E + N • A).GeneratesAt x (w a) := by
  filter_upwards [AmpleDominates.eventually_isGenerated q hL (isLB_toLB (-E))] with N hN
  have P := presents_toLB (E + N • A)
  obtain ⟨m, u, hu⟩ := hN.of_lbIso P.isLB ((cls_eq_iff P.isLB hN.isLB).1 (by
    rw [cls_div (isLB_lbPow hL.isLB N) (isLB_toLB _), cls_lbPow hL.isLB, ← toPic_apply, ← toPic_apply, map_add,
      map_nsmul, map_neg, hA]
    abel))
  refine ⟨m, fun a => P.rat (u a), fun a => CartierDiv.mem_sections.1 (P.rat_mem _), fun x => ?_⟩
  obtain ⟨a, ha⟩ := Opens.mem_iSup.1 (hu.ge (Set.mem_univ x))
  exact ⟨a, (P.generatesAt_rat_iff _).2 ha⟩

theorem exists_unitAt {x : X} {ι : Type} [Fintype ι] {c g : ι → X.functionField} (hc : ∀ i, RegAt x (c i))
    (hg : ∀ i, RegAt x (g i)) (e : ∑ i, c i * g i = 1) : ∃ i, UnitAt x (g i) := by
  by_contra! H
  have : ZeroAt x (∑ i, c i * g i) := Finset.sum_induction _ _ (fun _ _ => ZeroAt.add) (zeroAt_zero x) fun i _ =>
    mul_comm (g i) (c i) ▸ (zeroAt_iff.2 ⟨hg i, H i⟩).mul (hc i)
  exact (zeroAt_iff.1 (e ▸ this)).2 (unitAt_one x)

theorem exists_common_open {x : X} {ι : Type} [Finite ι] {g : ι → X.functionField} (hg : ∀ i, RegAt x (g i)) :
    ∃ (W : X.Opens) (hx : x ∈ W), ∀ i, ∃ a : Γ(X, W), fnOf W (gen_mem hx) a = g i := by
  choose U hU a ha using fun i => (hg i).exists_fnOf
  let W : X.Opens := ⟨⋂ i, U i, isOpen_iInter_of_finite fun i => (U i).isOpen⟩
  have hle (i) : W ≤ U i := Set.iInter_subset (fun i => (U i : Set X)) i
  exact ⟨W, Set.mem_iInter.2 hU, fun i => ⟨resG X (hle i) (a i), (fnOf_resG _ _ _).trans (ha i)⟩⟩

end General

variable {F : Type} [Field F] [NumberField F]

theorem exists_model_ratio {Y : Var F} (M : TrueGeo.Model Y) (E : Y.Dv) {n : ℕ} (w : Fin (n + 1) → Y.H0 E)
    (hw : ∀ x, ∃ a, E.GeneratesAt x (w a : Y.Fn)) :
    ∃ (N : TrueGeo.Model Y) (π : N.X ⟶ M.X), N.j ≫ π = M.j ∧ π ≫ M.p = N.p ∧ haveI := N.ar.isIntegral
      ∀ x : N.X, ∃ a, (w a : Y.Fn) ≠ 0 ∧ ∀ b, ∃ g, RegAt x g ∧ fnMap N.j (j_gen_specializes N) g * w a = w b := by
  have P := presents_toLB E
  let t : Fin (n + 1) → (Y.lb E).Sec := fun a => Var.sec (w a)
  have hgen (a) (x : Y.X) : E.GeneratesAt x (w a : Y.Fn) ↔ x ∈ nonzeroLocus (t a) := by
    rw [← P.generatesAt_rat_iff, Var.rat_sec]
  have ht : ⨆ a, nonzeroLocus (t a) = ⊤ := top_le_iff.1 fun x _ =>
    have ⟨a, ha⟩ := hw x
    Opens.mem_iSup.2 ⟨a, (hgen a x).1 ha⟩
  let c := Y.str ≫ spMap (algebraMap (𝓞 F) F)
  obtain ⟨X, q, j, hX, hq, hfl, H, ⟨π, hπ₁, hπ₂⟩, g, hg₁, hg₂⟩ := IntModel.exists_flat_model_two (O := 𝓞 F) Y.str
    Y.isProjOver M.ar.isProjOver ⟨n, 𝟙 _, inferInstance, Category.id_comp _⟩ M.pb.w (ProjSpace.toProj_str c t ht)
  have := CommonModel.isProper_of_isProjOver hq
  have hZ : Flat (spMap (Int.castRingHom (𝓞 F))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact (RingHom.flat_algebraMap_iff (R := ℤ) (S := 𝓞 F)).2 inferInstance
  have har : IsArithVar q Y.dim := ⟨inferInstance, inferInstance, hX, hq, inferInstance,
    IntModel.topologicalKrullDim_eq_succ (RingOfIntegers.not_isField F) H Y.topologicalKrullDim_eq⟩
  let N : TrueGeo.Model Y := ⟨X, q, har, j, H⟩
  refine ⟨N, π, hπ₁, hπ₂, fun x => ?_⟩
  obtain ⟨a, ha⟩ := ProjSpace.exists_mem_chart (𝓞 F) n (g x)
  let W : X.Opens := g ⁻¹ᵁ ProjSpace.chart (𝓞 F) n a
  have hx : x ∈ W := ha
  have hη : j (genericPoint Y.X) ⤳ genericPoint X := j_gen_specializes N
  have h : genericPoint Y.X ∈ j ⁻¹ᵁ W := hη.mem_open W.isOpen (gen_mem hx)
  have hU₀ : j ⁻¹ᵁ W ≤ (j ≫ g) ⁻¹ᵁ ProjSpace.chart (𝓞 F) n a := le_rfl
  have hU : j ⁻¹ᵁ W ≤ ProjSpace.toProj c t ht ⁻¹ᵁ ProjSpace.chart (𝓞 F) n a := hg₁ ▸ hU₀
  refine ⟨a, ((hgen _ _).2 ((ProjSpace.toProj_preimage_chart c t ht _).le (hU h))).ne_zero, fun b =>
    ⟨_, regAt_fnOf hx (gen_mem hx) (ProjSpace.pullRatio g W a le_rfl b), ?_⟩⟩
  have hf : j.app W (ProjSpace.pullRatio g W a le_rfl b) = ProjSpace.pullRatio (ProjSpace.toProj c t ht) _ a hU b := by
    refine Eq.trans ?_ (ProjSpace.pullRatio_of_eq hg₁ hU₀ _)
    rw [Scheme.Hom.app_eq_appLE]
    exact congrArg (fun ψ => ψ.hom (ProjSpace.ratio (𝓞 F) n a b)) (Scheme.Hom.appLE_comp_appLE j g _ _ _ le_rfl le_rfl)
  obtain ⟨m, hm⟩ := exists_chart P.isLB (genericPoint Y.X)
  have e := congrArg (fnOf _ (memInf h hm)) (ProjSpace.sec_eq_pullRatio_toProj_mul c t ht a b m
    (W := j ⁻¹ᵁ W ⊓ (Y.lb E).U m) (inf_le_left.trans hU) inf_le_right)
  rw [map_mul, fnOf_resG, fnOf_resG, ← P.rat_mul, ← P.rat_mul, Var.rat_sec, Var.rat_sec,
    ← ProjSpace.resG_pullRatio (hi := hU) inf_le_left, fnOf_resG, ← mul_assoc] at e
  rw [mul_right_cancel₀ (Units.ne_zero _) e, ← hf]
  exact congrArg (· * _) (fnMap_fnOf j hη _ h _)

theorem exists_family {Y : Var F} (M : TrueGeo.Model Y) (Δ : Y.Dv) (t : Y.X → Y.Fnˣ) (V : M.X.Opens) (d n : ℕ)
    (s : Fin n → Y.Fn) (z : M.X) (ht : ∀ y, Δ.IsEqn y (t y)) (hz : z ∈ V) (hs : Generates M t V d s) :
    ∃ (V' : M.X.Opens) (h : genericPoint Y.X ∈ M.j ⁻¹ᵁ V') (E : Y.Dv) (m : ℕ) (w : Fin (m + 1) → Y.H0 E),
      z ∈ V' ∧ V' ≤ V ∧ (∀ x, ∃ a, E.GeneratesAt x (w a : Y.Fn)) ∧ (∀ k, ∃ a, (w a : Y.Fn) = s k) ∧
      ∀ a, ∃ c : Fin n → Γ(M.X, V'), (w a : Y.Fn) = ∑ k, fnOf _ h (M.j.app V' (c k)) * s k := by
  classical
  have := M.ar.isIntegral
  have := isPreimmersion_j M
  have hη := j_gen_specializes M
  obtain ⟨H, hH⟩ := exists_isAmpleLB_of_isProjOver M.ar.isProjOver
  obtain ⟨e, he, σ, hzσ, hle, hV⟩ := hH.exists_affine_le hz
  have : IsAffineHom M.j := MorphismProperty.of_isPullback M.pb.flip (isAffineHom_of_isAffine _)
  have hL := ((isAmpleLB_pow_iff hH.isLB he).2 hH).pull_of_isAffineHom M.j
  have hloc := GlobalTheory.nonzeroLocus_secPull σ M.j
  set V' := nonzeroLocus σ
  have h₀ : genericPoint M.X ∈ V' := gen_mem hzσ
  have h : genericPoint Y.X ∈ M.j ⁻¹ᵁ V' := hη.mem_open V'.isOpen h₀
  obtain ⟨A, hA, hAL, hA'⟩ := exists_div_sec hL.isLB (GlobalTheory.secPull σ M.j) (hloc.ge h)
  simp only [hloc] at hA'
  have := hL.compactSpace
  have := CommonModel.isProper_of_isProjOver Y.isProjOver
  have hD (y) : (d • -Δ).IsEqn y ((t y)⁻¹ ^ d) := (ht y).neg.nsmul d
  obtain ⟨N, h₁, m, u, hu, hu'⟩ := ((Filter.eventually_all.2 fun k => eventually_regularAt hA (d • -Δ) (f := s k)
    fun y hy => ⟨_, hD y, (hs y (hle ((hA' y).1 hy))).1 k⟩).and
    (eventually_generates Y.str hL hAL (d • -Δ))).exists
  have hE (y) (hy : y ∈ M.j ⁻¹ᵁ V') : (d • -Δ + N • A).IsEqn y ((t y)⁻¹ ^ d) := by
    have h1 : A.IsEqn y 1 := CartierDiv.isEqn_iff_generatesAt_inv.2 (by simpa using (hA' y).2 hy)
    simpa using (hD y).add (h1.nsmul N)
  choose s' hs' using fun k => fnMap_surjective M.j hη (s k)
  have key (a) : ∃ b : Y.Fn, (∀ y, UnitAt y b) ∧ ∃ c : Fin n → Γ(M.X, V'),
      b * u a = ∑ k, fnOf _ h (M.j.app V' (c k)) * s k := by
    obtain ⟨u', hu₁⟩ := fnMap_surjective M.j hη (u a)
    obtain ⟨b, hb, c, hc⟩ := exists_comb M.p hV h₀ s' u' fun x hx hp => by
      obtain ⟨y, rfl⟩ := mem_range_j M hp
      obtain ⟨i, hi⟩ := (hs y (hle hx)).2
      have hr := ((hE y hx).regularAt_iff.1 (hu a y)).mul hi.inv.regAt
      have hi0 : s i ≠ 0 := left_ne_zero_of_mul hi.ne_zero
      rw [mul_inv, mul_mul_mul_comm, mul_inv_cancel₀ (Units.ne_zero _), mul_one] at hr
      refine ⟨i, u' * (s' i)⁻¹, (regAt_fnMap_iff M.j hη).1 (by rwa [map_mul, map_inv₀, hu₁, hs']), ?_⟩
      rw [inv_mul_cancel_right₀]
      intro h0
      exact hi0 (by rw [← hs', h0, map_zero])
    refine ⟨fnMap M.j hη (fnOf ⊤ trivial (algX M.p ⊤ b)), fun y => ?_, c, ?_⟩
    · rw [fnMap_fnOf M.j hη (U := ⊤) trivial trivial]
      refine (unitAt_fnOf_iff (U := M.j ⁻¹ᵁ ⊤) trivial _ _).2 ((Scheme.preimage_basicOpen M.j _).le ?_)
      exact (mem_basicOpen_algX M.p ⊤ b _).2 ⟨trivial, by rw [asIdeal_p_j]; exact hb⟩
    · have e₁ := congrArg (fnMap M.j hη) hc
      have e₂ : fnOf V' h₀ (algX M.p V' b) = fnOf ⊤ trivial (algX M.p ⊤ b) :=
        RingHom.congr_fun (fnOf_comp_algX M.p V' h₀) b
      simp only [e₂, map_mul, map_sum, hu₁, hs', fnMap_fnOf M.j hη h₀ h] at e₁
      exact e₁
  choose b hb c hc using key
  let w : Option (Fin n ⊕ Fin m) → Y.H0 (d • -Δ + N • A) := fun i => i.elim 0 (Sum.elim
    (fun k => ⟨s k, Var.mem_riemannRochSpace_iff_regularAt_everywhere.2 (h₁ k)⟩) fun a => ⟨b a * u a, Var.mem_riemannRochSpace_iff_regularAt_everywhere.2 fun y => (hu a y).regAt_mul (hb a y).regAt⟩)
  let ε : Fin (n + m + 1) ≃ Option (Fin n ⊕ Fin m) := (finSuccEquiv _).trans finSumFinEquiv.symm.optionCongr
  refine ⟨V', h, _, n + m, fun i => w (ε i), hzσ, hle, fun y => ?_,
    fun k => ⟨ε.symm (some (.inl k)), by beta_reduce; rw [ε.apply_symm_apply]; rfl⟩, fun i => ?_⟩
  · obtain ⟨a, g, hg, ha⟩ := hu' y
    refine ⟨ε.symm (some (.inr a)), g, hg, ?_⟩
    beta_reduce
    rw [ε.apply_symm_apply]
    change UnitAt y (b a * u a * g)
    rw [mul_assoc]
    exact (hb a y).mul ha
  · beta_reduce
    rcases ε i with _ | k | a
    · exact ⟨0, by simp [w]⟩
    · refine ⟨Pi.single k 1, ?_⟩
      rw [Finset.sum_eq_single k (fun j _ hj => by rw [Pi.single_eq_of_ne hj, map_zero, map_zero, zero_mul]) (by simp),
        Pi.single_eq_same, map_one, map_one, one_mul]
      rfl
    · exact ⟨c a, hc a⟩

theorem main : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (M : GlobalTheory.TrueGeo.Model Y) (Δ : Y.Dv)
    (t : Y.X → Y.Fnˣ) (V : M.X.Opens) (d n : ℕ) (s : Fin n → Y.Fn) (z : M.X), (∀ y, Δ.IsEqn y (t y)) → z ∈ V →
    Generates M t V d s → ∃ (N : GlobalTheory.TrueGeo.Model Y) (π : N.X ⟶ M.X) (V' : M.X.Opens), N.j ≫ π = M.j ∧
      π ≫ M.p = N.p ∧ z ∈ V' ∧ V' ≤ V ∧ ∀ x ∈ π ⁻¹ᵁ V', ∃ (i : Fin n) (W : N.X.Opens), x ∈ W ∧ s i ≠ 0 ∧
        ∀ k, ∃ g : Γ(N.X, W), ∀ h : genericPoint Y.X ∈ N.j ⁻¹ᵁ W, fnOf (N.j ⁻¹ᵁ W) h (N.j.app W g) * s i = s k := by
  intro F _ _ Y M Δ t V d n s z ht hz hs
  obtain ⟨V', h, E, m, w, hz', hle, hw, hw₁, hw₂⟩ := exists_family M Δ t V d n s z ht hz hs
  obtain ⟨N, π, hπ₁, hπ₂, hN⟩ := exists_model_ratio M E w hw
  have := N.ar.isIntegral
  have hη := j_gen_specializes N
  refine ⟨N, π, V', hπ₁, hπ₂, hz', hle, fun x hx => ?_⟩
  obtain ⟨a, ha, hb⟩ := hN x
  obtain ⟨c, hc⟩ := hw₂ a
  have hg (k) : ∃ g, RegAt x g ∧ fnMap N.j hη g * w a = s k := by
    obtain ⟨b, e⟩ := hw₁ k
    exact e ▸ hb b
  choose g hg hg' using hg
  have e (k) : fnMap N.j hη (fnOf _ (gen_mem hx) (π.app V' (c k))) = fnOf _ h (M.j.app V' (c k)) := by
    have gen {j : Y.X ⟶ M.X} (hj : N.j ≫ π = j) (h : genericPoint Y.X ∈ j ⁻¹ᵁ V') :
        fnMap N.j hη (fnOf _ (gen_mem hx) (π.app V' (c k))) = fnOf _ h (j.app V' (c k)) := by
      subst hj
      exact fnMap_fnOf N.j hη (U := π ⁻¹ᵁ V') _ h _
    exact gen hπ₁ h
  obtain ⟨i, hi⟩ := exists_unitAt (x := x) (fun k => regAt_fnOf hx (gen_mem hx) (π.app V' (c k))) hg (by
    apply (fnMap N.j hη).injective
    apply mul_right_cancel₀ ha
    rw [map_one, one_mul, map_sum, Finset.sum_mul]
    refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_) hc.symm
    rw [map_mul, e, mul_assoc, hg'])
  obtain ⟨W, hW, hW'⟩ := exists_common_open fun k => (hg k).mul hi.inv.regAt
  have h0 : fnMap N.j hη (g i) ≠ 0 := (map_ne_zero _).2 hi.ne_zero
  refine ⟨i, W, hW, hg' i ▸ mul_ne_zero h0 ha, fun k => ?_⟩
  obtain ⟨γ, hγ⟩ := hW' k
  refine ⟨γ, fun h' => ?_⟩
  rw [← fnMap_fnOf N.j hη (gen_mem hW) h', hγ, ← hg' i, ← hg' k, map_mul, map_inv₀, mul_assoc,
    inv_mul_cancel_left₀ h0]

end GlobalTheory.InvertIdeal
