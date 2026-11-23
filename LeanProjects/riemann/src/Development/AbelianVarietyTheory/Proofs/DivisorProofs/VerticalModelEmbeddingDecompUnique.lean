import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsBaseEqChain
import Development.AbelianVarietyTheory.Definitions.Divisors.FaithfulSMulAlgClosure
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoRestrictPushforwardUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EAComm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameLocal

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison GlobalTheory.ChainPts
open GlobalTheory.ChainParts
open GlobalTheory.Twist (resM app_resM resM_resM resM_smul sec_ext_of_cover resM_self)
open scoped Classical

namespace GlobalTheory.ChainPts.PartDual

theorem sec_eq_zero {X : Scheme.{0}} [IsIntegral X] {F : X.Modules} {r : ℕ} (hF : VB.IsVB F r) {U W : X.Opens}
    (hU : (U : Set X).Nonempty) (t : Γ(F, W)) (ht : resM F (inf_le_left : W ⊓ U ≤ W) t = 0) : t = 0 := by
  choose V f hx hf using hF
  refine sec_ext_of_cover (fun x : W => W ⊓ V x) (fun _ => inf_le_left)
    (fun x hW => Opens.mem_iSup.2 ⟨⟨x, hW⟩, hW, hx x⟩) fun x => ?_
  rw [map_zero]
  refine ((hf x).basis inf_le_right).ext_elem fun i => ?_
  have hne : ((W ⊓ V x ⊓ U : X.Opens) : Set X).Nonempty :=
    nonempty_preirreducible_inter (W ⊓ V x).isOpen U.isOpen ⟨x, x.2, hx x⟩ hU
  haveI : Nonempty (W ⊓ V x ⊓ U : X.Opens) := hne.to_subtype
  apply map_injective_of_isIntegral X (homOfLE (inf_le_left : W ⊓ V x ⊓ U ≤ W ⊓ V x))
  have h1 := (hf x).repr_resM inf_le_right (inf_le_left : W ⊓ V x ⊓ U ≤ W ⊓ V x) (resM F inf_le_left t) i
  have h2 : resM F (inf_le_left : W ⊓ V x ⊓ U ≤ W ⊓ V x) (resM F inf_le_left t) = 0 := by
    rw [resM_resM, ← resM_resM (inf_le_left : W ⊓ U ≤ W) (inf_le_inf_right U inf_le_left), ht, map_zero]
  rw [h2, map_zero] at h1
  rw [map_zero]
  simp only [Finsupp.zero_apply, map_zero] at h1 ⊢
  exact h1.symm

theorem hom_eq_zero {X : Scheme.{0}} [IsIntegral X] {F G : X.Modules} {r n : ℕ} (hG : VB.IsVB G r) {U : X.Opens}
    (hU : (U : Set X).Nonempty) {s : Fin n → Γ(F, U)} (hs : VB.IsFrame s) (φ : F ⟶ G) (h : ∀ j, φ.app U (s j) = 0) :
    φ = 0 := by
  refine Scheme.Modules.hom_ext _ _ fun W => ?_
  ext t
  refine sec_eq_zero hG hU _ ?_
  rw [← app_resM]
  obtain ⟨a, ha⟩ := (hs (W ⊓ U) inf_le_right).2 (resM F inf_le_left t)
  rw [← ha, Fintype.linearCombination_apply]
  change QCoh.appLinear φ _ _ = 0
  rw [map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [map_smul, QCoh.appLinear_apply, app_resM, h, map_zero, smul_zero]

section Part

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {B : Vert.Model O} {Λ : Type} [CommRing Λ]

theorem eA_app (M : AM B Λ) {n : ℕ} (c : Fin n → Γ(B.X, ⊤)) (b : Fin n → Λ) {U : B.X.Opens} (s : Γ(M.V, U))
    (lam : Fin n → Γ(B.X, U)) (hs : ∀ k, (M.ρ (b k) : M.V ⟶ M.V).app U s = lam k • s) :
    (eA M c b).app U s = (∑ k, restrictGlobal B.X U (c k) * lam k) • s := by
  have hsum : ∀ (t : Finset (Fin n)) (φ : Fin n → (M.V ⟶ M.V)),
      (∑ k ∈ t, φ k).app U s = ∑ k ∈ t, (φ k).app U s := by
    intro t φ
    induction t using Finset.induction_on with
    | empty => simp
    | insert a t ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Scheme.Modules.Hom.add_app, ← ih]
      rfl
  rw [eA, hsum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← QCoh.app_app, smulHom_app_apply]
  change QCoh.appLinear (M.ρ (b k) : M.V ⟶ M.V) U _ = _
  rw [map_smul, QCoh.appLinear_apply, hs, smul_smul]

def partπ {n : ℕ} (c : Fin n → Γ(B.X, ⊤)) (b : Fin n → Λ) (M : AM B Λ) (h : eA M c b ≫ eA M c b = eA M c b) :
    M.V ⟶ (partF c b).obj M :=
  kernel.lift _ (eA M c b) (by rw [Preadditive.comp_sub, h, Category.comp_id, sub_self])

theorem partπ_ι {n : ℕ} (c : Fin n → Γ(B.X, ⊤)) (b : Fin n → Λ) (M : AM B Λ) (h : eA M c b ≫ eA M c b = eA M c b) :
    partπ c b M h ≫ partι c b M = eA M c b := kernel.lift_ι _ _ _

theorem mono_partι {n : ℕ} (c : Fin n → Γ(B.X, ⊤)) (b : Fin n → Λ) (M : AM B Λ) : Mono (partι c b M) :=
  inferInstanceAs (Mono (kernel.ι _))

theorem partι_π {n : ℕ} (c : Fin n → Γ(B.X, ⊤)) (b : Fin n → Λ) (M : AM B Λ) (h : eA M c b ≫ eA M c b = eA M c b) :
    partι c b M ≫ partπ c b M h = 𝟙 _ := by
  haveI := mono_partι c b M
  rw [← cancel_mono (partι c b M), Category.assoc, partπ_ι, Category.id_comp]
  have : partι c b M ≫ (𝟙 M.V - eA M c b) = 0 := kernel.condition _
  rw [Preadditive.comp_sub, Category.comp_id, sub_eq_zero] at this
  exact this.symm

theorem partπ_comm {n : ℕ} (c : Fin n → Γ(B.X, ⊤)) (b : Fin n → Λ) {M N : AM B Λ} (f : M ⟶ N)
    (h : eA M c b ≫ eA M c b = eA M c b) (h' : eA N c b ≫ eA N c b = eA N c b) :
    partπ c b M h ≫ (partF c b).map f = f.hom ≫ partπ c b N h' := by
  haveI := mono_partι c b N
  have e : (partF c b).map f ≫ partι c b N = partι c b M ≫ f.hom := kernel.lift_ι _ _ _
  rw [← cancel_mono (partι c b N), Category.assoc, e, ← Category.assoc, partπ_ι, Category.assoc, partπ_ι, eA_comm]

theorem idem_of_frame {X : Scheme.{0}} [IsIntegral X] {F : X.Modules} {r n : ℕ} (hF : VB.IsVB F r) {U : X.Opens}
    (hU : (U : Set X).Nonempty) {s : Fin n → Γ(F, U)} (hs : VB.IsFrame s) (e : F ⟶ F) (ε : Fin n → Prop) [DecidablePred ε]
    (h : ∀ j, e.app U (s j) = (if ε j then (1 : Γ(X, U)) else 0) • s j) : e ≫ e = e := by
  rw [← sub_eq_zero]
  refine hom_eq_zero hF hU hs _ fun j => ?_
  rw [Scheme.Modules.Hom.sub_app]
  change (e ≫ e).app U (s j) - e.app U (s j) = 0
  rw [← QCoh.app_app, sub_eq_zero]
  have := h j
  split_ifs at this
  · rw [one_smul] at this
    rw [this, this]
  · rw [zero_smul] at this
    rw [this, map_zero]

theorem rank_eq_of_frame {X : Scheme.{0}} {F : X.Modules} {r n : ℕ} (hF : VB.IsVB F r) {U : X.Opens}
    (hU : (U : Set X).Nonempty) {s : Fin n → Γ(F, U)} (hs : VB.IsFrame s) : r = n := by
  obtain ⟨x, hx⟩ := hU
  rw [← hF.finrank_stalk x, Module.finrank_eq_card_basis (hs.stalkBasis x hx), Fintype.card_fin]

end Part

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

theorem isLat_part (Z : LocM.Mdl Y i₀) {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {B : Vert.Model O}
    {Λ : Type} [CommRing Λ] (h : B.X ⟶ Z.X) {r r' r₀ : ℕ} (hr : r₀ = r) (x : Fin r → Letter Dw) (σ : Fin r' → Fin r)
    (hσ : Function.Injective σ) (d β : Bool) (M : AM B Λ) (hM : VB.IsVB M.V r₀) {n : ℕ} (c : Fin n → Γ(B.X, ⊤))
    (b : Fin n → Λ) (s : ∀ a : Fin Z.m, Fin r → Γ(M.V, h ⁻¹ᵁ (Z.U a).1)) (hs : IsLat Z h x d β M.V s)
    (he : ∀ a j, (eA M c b).app _ (s a j) = (if j ∈ Set.range σ then (1 : Γ(B.X, h ⁻¹ᵁ (Z.U a).1)) else 0) • s a j)
    (hi : eA M c b ≫ eA M c b = eA M c b) :
    IsLat Z h (fun k => x (σ k)) d β ((partF c b).obj M) (fun a k => (partπ c b M hi).app _ (s a (σ k))) := by
  subst hr
  refine SummandLat.isLat_summand Z h (partι c b M) (partπ c b M hi) (partι_π c b M hi) σ hσ hM x d β s hs
    (fun a k => ?_) (fun a j hj => ?_)
  · rw [QCoh.app_app, partπ_ι, he, if_pos ⟨k, rfl⟩, one_smul]
  · have h1 : (partι c b M).app _ ((partπ c b M hi).app _ (s a j)) = 0 := by
      rw [QCoh.app_app, partπ_ι, he, if_neg hj, zero_smul]
    have h2 := congrArg ((partπ c b M hi).app _) h1
    rwa [QCoh.app_app, partι_π, map_zero] at h2

theorem isLatPres_part (Z : LocM.Mdl Y i₀) {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {B : Vert.Model O} (h : B.X ⟶ Z.X) (hne : ∃ a, ((h ⁻¹ᵁ (Z.U a).1 : B.X.Opens) : Set B.X).Nonempty) {r r' : ℕ}
    (x : Fin r → Letter Dw) (σ : Fin r' → Fin r) (hσ : Function.Injective σ) (d : Bool) (P : EPres B (𝓞 E))
    (hP : IsEqLatPres Z h x d P) {n : ℕ} (c : Fin n → Γ(B.X, ⊤)) (b : Fin n → 𝓞 E)
    (hc : ∀ (a : Fin Z.m) (j : Fin r), ∑ k, restrictGlobal B.X (h ⁻¹ᵁ (Z.U a).1) (c k) *
      (h.app (Z.U a).1).hom (Z.alg a (embK Z.i.c (x j).1 (if d then H.bar (b k) else b k))) =
        if j ∈ Set.range σ then 1 else 0) (r₁ : ℕ) vb vb' iso :
    IsLatPres Z h (fun k => x (σ k)) d ⟨r₁, (partF c b).obj P.E, (partF c b).obj P.E', vb, vb', (partF c b).map P.ψ, iso⟩ := by
  obtain ⟨hr, s, h1, h2, h3⟩ := hP
  obtain ⟨a₀, ha₀⟩ := hne
  have e1 : ∀ a j, (eA P.E' c b).app _ (s a j) =
      (if j ∈ Set.range σ then (1 : Γ(B.X, h ⁻¹ᵁ (Z.U a).1)) else 0) • s a j := fun a j => by
    rw [eA_app P.E' c b (s a j) _ (fun k => h3 a j (b k)), hc]
  have e2 : ∀ a j, (eA P.E c b).app _ (P.ψ.hom.app _ (s a j)) =
      (if j ∈ Set.range σ then (1 : Γ(B.X, h ⁻¹ᵁ (Z.U a).1)) else 0) • P.ψ.hom.app _ (s a j) := fun a j => by
    rw [QCoh.app_app, ← eA_comm, ← QCoh.app_app, e1]
    exact (QCoh.appLinear P.ψ.hom _).map_smul _ _
  have i1 := idem_of_frame P.vb' ha₀ (h1.frame a₀) _ _ (e1 a₀)
  have i2 := idem_of_frame P.vb ha₀ (h2.frame a₀) _ _ (e2 a₀)
  have l1 := isLat_part Z h hr x σ hσ d d P.E' P.vb' c b s h1 e1 i1
  have l2 := isLat_part Z h hr x σ hσ d (!d) P.E P.vb c b _ h2 e2 i2
  refine ⟨rank_eq_of_frame vb' ha₀ (l1.frame a₀), _, l1, ?_⟩
  have e : (fun (a : Fin Z.m) (k : Fin r') => ((partF c b).map P.ψ).app (h ⁻¹ᵁ (Z.U a).1)
      ((partπ c b P.E' i1).app _ (s a (σ k)))) =
      fun a k => (partπ c b P.E i2).app _ (P.ψ.hom.app _ (s a (σ k))) := by
    funext a k
    rw [QCoh.app_app, QCoh.app_app, partπ_comm c b P.ψ i1 i2]
  exact e ▸ l2

theorem const_chart (Z : LocM.Mdl Y i₀) (a : Fin Z.m) (v : Z.i.c.V W) :
    restrictGlobal Z.X (Z.U a).1 (Z.s.appTop ((Scheme.ΓSpecIso (.of (Z.i.c.V W))).inv v)) = Z.alg a (v : Z.i.c.F) := by
  have h1 : Z.s = Z.X.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (.of (Z.i.c.V W))).inv ≫ Z.s.appTop) := by
    rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  have h2 := Z.alg_s a
  have h0 : Z.chart a ≫ Z.X.toSpecΓ = _ := IsAffineOpen.fromSpec_toSpecΓ (Z.U a).2
  rw [h1, ← Category.assoc, h0, ← Spec.map_comp] at h2
  have h3 := congrArg (fun φ => φ.hom v) (Spec.map_injective h2)
  exact h3

theorem const_pull (Z : LocM.Mdl Y i₀) [IsDiscreteValuationRing (Z.i.c.V W)] {B : Vert.Model (Z.i.c.V W)} (h : B.X ⟶ Z.X)
    (hh : h ≫ Z.s = B.str) (a : Fin Z.m) (v : Z.i.c.V W) :
    restrictGlobal B.X (h ⁻¹ᵁ (Z.U a).1) (B.const v) = (h.app (Z.U a).1).hom (Z.alg a (v : Z.i.c.F)) := by
  rw [← const_chart, Vert.Model.const, Vert.Model.const_eq, ← hh, Scheme.Hom.comp_appTop]
  exact (congrArg (fun φ => φ.hom (Z.s.appTop ((Scheme.ΓSpecIso (.of (Z.i.c.V W))).inv v)))
    (h.naturality (homOfLE (le_top : (Z.U a).1 ≤ ⊤)).op)).symm

theorem exists_chart_nonempty (Z : LocM.Mdl Y i₀) [IsDiscreteValuationRing (Z.i.c.V W)] (c : (nmodel Z).Comp)
    (B : Vert.Model (Z.i.c.V W)) (f : Vert.Model.Hom B ((nmodel Z).comp c)) :
    ∃ a, (((f.f ≫ (nmodel Z).compι c) ⁻¹ᵁ (Z.U a).1 : B.X.Opens) : Set B.X).Nonempty := by
  have hc : ((c.opens : Z.X.Opens) : Set Z.X).Nonempty := by
    obtain ⟨y⟩ : Nonempty ((nmodel Z).comp c).X := inferInstance
    exact ⟨y.1, y.2⟩
  obtain ⟨y, hy, hy'⟩ := Z.dense.inter_open_nonempty _ c.opens.isOpen hc
  rw [← Z.cover] at hy'
  obtain ⟨a, ha⟩ := Set.mem_iUnion.1 hy'
  obtain ⟨w, hw⟩ := f.f.surjective (show ((nmodel Z).comp c).X from ⟨y, hy⟩)
  refine ⟨a, w, ?_⟩
  change (f.f ≫ (nmodel Z).compι c) w ∈ (Z.U a).1
  rw [Scheme.Hom.comp_apply, hw]
  exact ha

theorem embK_bar' {l : Level H} (c : Coeff l) (τ : E →+* ℂ) (a : 𝓞 E) :
    embK c τ (H.bar a) = embK c (conjEmb τ) a := by
  apply Subtype.ext
  rw [embK_coe, embK_coe, H.bar_eq, conjEmb, RingHom.comp_apply]
  rw [← ComplexEmbedding.conjugate_coe_eq, IsCMField.complexEmbedding_complexConj]
  simp

theorem conjEmb_conjEmb' (τ : E →+* ℂ) : conjEmb (conjEmb τ) = τ := by
  ext a
  simp [conjEmb]

theorem scalar_eq (Z : LocM.Mdl Y i₀) [IsDiscreteValuationRing (Z.i.c.V W)] {B : Vert.Model (Z.i.c.V W)} (h : B.X ⟶ Z.X)
    (hh : h ≫ Z.s = B.str) (a : Fin Z.m) {n : ℕ} (b : Fin n → 𝓞 E) (cf : Fin n → Z.i.c.V W) (ev : 𝓞 E →+* Z.i.c.V W)
    (τ : E →+* ℂ) (hev : ∀ x, ((ev x : Z.i.c.V W) : Z.i.c.F) = embK Z.i.c (conjEmb τ) x) {q q' : Prop} {dq : Decidable q}
    {dq' : Decidable q'} (hq : q ↔ q') (hcf : ∑ k, cf k * ev (b k) = if q' then 1 else 0) :
    ∑ k, restrictGlobal B.X (h ⁻¹ᵁ (Z.U a).1) (B.const (cf k)) *
      (h.app (Z.U a).1).hom (Z.alg a (embK Z.i.c τ (if true then H.bar (b k) else b k))) = if q then 1 else 0 := by
  have h1 : ∑ k, restrictGlobal B.X (h ⁻¹ᵁ (Z.U a).1) (B.const (cf k)) *
      (h.app (Z.U a).1).hom (Z.alg a (embK Z.i.c τ (if true then H.bar (b k) else b k))) =
        restrictGlobal B.X (h ⁻¹ᵁ (Z.U a).1) (B.const (∑ k, cf k * ev (b k))) := by
    simp only [Vert.Model.const, map_sum, map_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [if_pos trivial, embK_bar', ← hev, ← const_pull Z h hh]
  have key : ∀ {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (u : R →+* S) (v : S →+* T),
      v (u (if q' then 1 else 0)) = if q then 1 else 0 := fun u v => by
    by_cases hh : q'
    · rw [if_pos hh, if_pos (hq.2 hh), map_one, map_one]
    · rw [if_neg hh, if_neg (mt hq.1 hh), map_zero, map_zero]
  exact h1.trans ((congrArg (fun t => restrictGlobal B.X (h ⁻¹ᵁ (Z.U a).1) (B.const t)) hcf).trans
    (key (algebraMap _ Γ(B.X, ⊤)) (restrictGlobal B.X _)))

theorem isLatPres_part_dual (Z : LocM.Mdl Y i₀) [IsDiscreteValuationRing (Z.i.c.V W)] (c : (nmodel Z).Comp)
    (B : Vert.Model (Z.i.c.V W)) (f : Vert.Model.Hom B ((nmodel Z).comp c)) {r r' : ℕ}
    (x : Fin r → Letter Dw) (x' : Fin r' → Letter Dw) (σ : Fin r' → Fin r) (hσ : Function.Injective σ)
    (hx : ∀ k, x (σ k) = x' k) (P : EPres B (𝓞 E))
    (hP : IsEqLatPres Z (f.f ≫ (nmodel Z).compι c) x true P) {n : ℕ} (cf : Fin n → Z.i.c.V W) (b : Fin n → 𝓞 E)
    (hc : ∀ j : Fin r, ∃ ev : 𝓞 E →+* Z.i.c.V W, (∀ y, ((ev y : Z.i.c.V W) : Z.i.c.F) = embK Z.i.c (conjEmb (x j).1) y) ∧
      ∑ k, cf k * ev (b k) = if j ∈ Set.range σ then 1 else 0) (r₁ : ℕ) vb vb' iso :
    IsLatPres Z (f.f ≫ (nmodel Z).compι c) x' true ⟨r₁, (partF (fun k => B.const (cf k)) b).obj P.E,
      (partF (fun k => B.const (cf k)) b).obj P.E', vb, vb', (partF (fun k => B.const (cf k)) b).map P.ψ, iso⟩ := by
  obtain rfl : (fun k => x (σ k)) = x' := funext hx
  have hh : (f.f ≫ (nmodel Z).compι c) ≫ Z.s = B.str := by
    rw [Category.assoc]
    exact f.comp_str
  refine isLatPres_part Z (f.f ≫ (nmodel Z).compι c) (exists_chart_nonempty Z c B f) x σ hσ true P hP
    (fun k => B.const (cf k)) b (fun a j => ?_) r₁ vb vb' iso
  obtain ⟨ev, h1, h2⟩ := hc j
  exact scalar_eq Z _ hh a b cf ev _ h1 Iff.rfl h2

end Free

theorem isLatPres_part_om : ∀ {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ} [Fact p.Prime] {hp : p.Prime} {W : ValuationSubring ℂ} {hW : (p : ℂ) ∈ W.nonunits} (z : AdmAt S κ hp hW) (jc : KW p →+* ℂ), haveI := isDiscreteValuationRing_V z.Z.i.c hp hW
    haveI := charP_residueField_of_mem_nonunits z.Z.i.c hp hW
    ∀ (c : (nmodel z.Z).Comp) (B : Vert.Model (z.Z.i.c.V W)) (f : Vert.Model.Hom B ((nmodel z.Z).comp c)) (n : ℕ)
      (b : Fin n → 𝓞 D.host.E) (ev : Emb D p → (𝓞 D.host.E →+* z.Z.i.c.V W)) (cf : Emb D p → Fin n → z.Z.i.c.V W),
      (∀ σ x, ((ev σ x : z.Z.i.c.V W) : z.Z.i.c.F) = embK z.Z.i.c (jc.comp σ) x) →
      (∀ σ' : D.host.E →+* ℂ, ∃ σ : Emb D p, σ' = jc.comp σ) →
      (∀ τ σ : Emb D p, ∑ k, cf τ k * ev σ (b k) = if σ = τ then 1 else 0) →
      ∀ P : EPres B (𝓞 D.host.E), IsEqLatPres z.Z (f.f ≫ (nmodel z.Z).compι c) (fun k => xAll S k.rev) true P →
      ∀ (τ : Emb D p) (r : ℕ) vb vb' iso, IsLatPres z.Z (f.f ≫ (nmodel z.Z).compι c) (xOm S jc τ) true
        ⟨r, (partF (fun k => B.const (cf τ k)) b).obj P.E, (partF (fun k => B.const (cf τ k)) b).obj P.E', vb, vb',
          (partF (fun k => B.const (cf τ k)) b).map P.ψ, iso⟩ := by
  intro D A N j S κ p _ hp W hW z jc
  haveI := isDiscreteValuationRing_V z.Z.i.c hp hW
  intro c B f n b ev cf hev hall hcf P hP τ r vb vb' iso
  have hb : Function.Bijective fun k => xAll S (Fin.rev k) := (xAll_bijective S).comp Fin.rev_bijective
  choose σ hσ using fun i => hb.2 (xOm S jc τ i)
  have hinj : Function.Injective (xOm S jc τ) := fun i i' h => by
    have : (i.rev : ℕ) = i'.rev := congrArg (fun x : Letter S.Dw => (x.2 : ℕ)) h
    exact Fin.rev_injective (Fin.ext this)
  have hσi : Function.Injective σ := fun i i' h => hinj (by rw [← hσ, ← hσ, h])
  have hrange : ∀ k, k ∈ Set.range σ ↔ (xAll S (Fin.rev k)).1 = conjEmb (jc.comp τ) := fun k => by
    constructor
    · rintro ⟨i, rfl⟩
      exact congrArg Sigma.fst (hσ i)
    · intro hk
      have : ∃ i, xOm S jc τ i = xAll S (Fin.rev k) := by
        generalize xAll S (Fin.rev k) = y at hk
        obtain ⟨y₁, y₂⟩ := y
        obtain rfl : y₁ = _ := hk
        exact ⟨(y₂.cast (mult_conj_comp S jc τ)).rev, by simp [xOm]⟩
      obtain ⟨i, hi⟩ := this
      exact ⟨i, hb.1 ((hσ i).trans hi)⟩
  refine isLatPres_part_dual z.Z c B f (fun k => xAll S k.rev) _ σ hσi hσ P hP (cf τ) b (fun k => ?_) r vb vb' iso
  obtain ⟨σ', hσ'⟩ := hall (conjEmb (xAll S k.rev).1)
  have hiff : k ∈ Set.range σ ↔ σ' = τ := by
    rw [hrange]
    constructor
    · intro h
      rw [h, conjEmb_conjEmb'] at hσ'
      exact RingHom.ext fun x => jc.injective (RingHom.congr_fun hσ' x).symm
    · rintro rfl
      rw [← hσ', conjEmb_conjEmb']
  refine ⟨ev σ', fun y => (hev σ' y).trans (congrArg (fun t => embK z.Z.i.c t y) hσ'.symm), (hcf τ σ').trans ?_⟩
  exact if_congr hiff.symm rfl rfl

end GlobalTheory.ChainPts.PartDual

end
