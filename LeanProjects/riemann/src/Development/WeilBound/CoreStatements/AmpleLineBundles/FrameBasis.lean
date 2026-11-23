import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeEvalAtLocalRing
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeFrameSpecializes
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SegreChartBundle
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsAtSmul
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace CoverDenseAlt.Met

open GlobalTheory.CompanionTheory.Ar.RootHt

theorem lat_val (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (Ω : Type) [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (R : Type)
    [CommRing R] [IsLocalRing R] (z : Spec (CommRingCat.of R) ⟶ X) (h : genPt ξ ⤳ centre z) (ER : Type)
    [AddCommGroup ER] [Module R ER] (MR : LieModel G z ER) :
    IsCptGen ξ → Smooth G.hom → ∃ ev : M.lat ⟨centre z, h⟩ →+ ER,
      (∀ (e : E) (w : ER), M.ValAt z e (MR.pt w) ↔ ∃ he : e ∈ M.lat ⟨centre z, h⟩, ev ⟨e, he⟩ = w) ∧
      (∀ (a : regAt ξ ⟨centre z, h⟩) (r : R) e, ValAt ξ z (a : Ω) r → ev (a • e) = r • ev e) ∧
      Submodule.span R (Set.range ev) = ⊤ := by
  intro hξ hs
  obtain ⟨EA, _, _, ⟨MA⟩⟩ := lieModel_exists X G (X.presheaf.stalk (centre z)) (X.fromSpecStalk (centre z))
  obtain ⟨j, hj, hjs, hjb⟩ := LieVal.exists_base (A := X.presheaf.stalk (centre z)) (Scheme.stalkClosedPointTo z).hom _ z
    (LieTangent.spec_centre z) MA MR
  obtain ⟨i, hi, his, -⟩ := LieVal.exists_base (genMap ξ ⟨centre z, h⟩) _ ξ
    (LieTangent.spec_genMap ξ ⟨centre z, h⟩) MA M

  have hext : ∀ a, M.Extends ⟨centre z, h⟩ (i a) (MA.pt a) := fun a => ⟨MA.tan a, hi a⟩
  have hmem : ∀ a, i a ∈ M.lat ⟨centre z, h⟩ := fun a => (M.mem_lat_iff _ _).2 ⟨_, hext a⟩
  have hinj : ∀ a b, i a = i b → a = b := fun a b hab =>
    MA.inj ((hext a).unique (hξ.inj _) (hab ▸ hext b))
  have hsurj : ∀ e v, M.Extends ⟨centre z, h⟩ e v → ∃ a, i a = e ∧ MA.pt a = v := by
    intro e v hv
    obtain ⟨a, rfl⟩ := MA.onto v hv.1
    exact ⟨a, M.inj (Over.OverMorphism.ext ((hi a).trans hv.2.symm)), rfl⟩
  let i' : EA →+ M.lat ⟨centre z, h⟩ :=
    { toFun := fun a => ⟨i a, hmem a⟩
      map_zero' := Subtype.ext (map_zero i)
      map_add' := fun a b => Subtype.ext (map_add i a b) }
  have hbij : Function.Bijective i' := by
    refine ⟨fun a b hab => hinj a b (congrArg Subtype.val hab), fun e => ?_⟩
    obtain ⟨v, hv⟩ := (M.mem_lat_iff _ _).1 e.2
    obtain ⟨a, ha, -⟩ := hsurj _ _ hv
    exact ⟨a, Subtype.ext ha⟩
  let q := AddEquiv.ofBijective i' hbij
  have hq : ∀ a, q.symm ⟨i a, hmem a⟩ = a := fun a => q.symm_apply_apply a
  refine ⟨j.comp q.symm.toAddMonoidHom, ?_, ?_, ?_⟩
  · intro e w
    constructor
    · rintro ⟨h', v, hv, hw⟩
      obtain ⟨a, rfl, rfl⟩ := hsurj _ _ hv
      refine ⟨hmem a, ?_⟩
      change j (q.symm ⟨i a, hmem a⟩) = w
      rw [hq]
      exact MR.inj (Over.OverMorphism.ext ((hj a).trans hw.symm))
    · rintro ⟨he, rfl⟩
      obtain ⟨v, hv⟩ := (M.mem_lat_iff _ _).1 he
      obtain ⟨a, rfl, rfl⟩ := hsurj _ _ hv
      change M.ValAt z (i a) (MR.pt (j (q.symm ⟨i a, hmem a⟩)))
      rw [hq]
      exact ⟨h, _, hext a, hj a⟩
  · rintro a r e ⟨_, s, hsa, rfl⟩
    obtain ⟨b, rfl⟩ := q.surjective e
    have : a • q b = q (s • b) := Subtype.ext (by
      change (a : Ω) • i b = i (s • b)
      rw [his, hsa])
    change j (q.symm (a • q b)) = _ • j (q.symm (q b))
    rw [this, q.symm_apply_apply, q.symm_apply_apply]
    exact hjs s b
  · obtain ⟨hfin, hproj, -⟩ := GlobalTheory.T.lie_model_finite_base_change X G (X.presheaf.stalk (centre z)) (X.fromSpecStalk (centre z)) EA MA
    have : Module.Free (X.presheaf.stalk (centre z)) EA := Module.free_of_flat_of_isLocalRing
    let n := Module.finrank (X.presheaf.stalk (centre z)) EA
    let b : Module.Basis (Fin n) (X.presheaf.stalk (centre z)) EA := Module.finBasis _ EA
    refine top_le_iff.1 ((hjb hs n b).symm.le.trans (Submodule.span_mono ?_))
    rintro _ ⟨k, rfl⟩
    refine ⟨q (b k), ?_⟩
    change j (q.symm (q (b k))) = _
    rw [q.symm_apply_apply]

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {G : Over X} [GrpObj G]
  {Li : Type} [AddCommGroup Li] [Module Ω Li] {r : ℕ}

theorem frame_basis [IsCommMonObj G] [Smooth G.hom] (hξ : IsCptGen ξ) (M : LieModel G ξ Li)
    (B : Module.Basis (Fin r) Ω Li) (z : Sp ℂ ⟶ X) (h : genPt ξ ⤳ centre z)
    (hB : M.lat.IsFrameAt B ⟨centre z, h⟩) {V : Type} [AddCommGroup V] [Module ℂ V] (Mz : LieModel G z V) :
    ∃ β : Module.Basis (Fin r) ℂ V, (∀ i u, M.ValAt z (B i) (Mz.pt u) ↔ u = β i) ∧
      ∀ e u, M.ValAt z e (Mz.pt u) → ∀ i, ValAt ξ z (B.repr e i) (β.repr u i) := by
  obtain ⟨ev, hev, hsm, hsp⟩ := lat_val X G Ω ξ Li M ℂ z h V Mz hξ inferInstance
  have hmem : ∀ i, B i ∈ M.lat ⟨centre z, h⟩ := fun i => by
    rw [hB.2]; exact Submodule.subset_span ⟨i, rfl⟩
  let b : Fin r → V := fun i => ev ⟨B i, hmem i⟩
  have key : ∀ e (he : e ∈ M.lat ⟨centre z, h⟩), ∃ c : Fin r → ℂ, (∀ i, ValAt ξ z (B.repr e i) (c i)) ∧
      ev ⟨e, he⟩ = ∑ i, c i • b i := by
    intro e he
    have hreg : ∀ i, B.repr e i ∈ regAt ξ ⟨centre z, h⟩ := fun i =>
      TieFrame.coords_mem (a := fun i => B.repr e i) hB.1 (by rw [B.sum_repr, ← hB.2]; exact he) i
    choose c hc using fun i => ArchB.val_exists (R := ℂ) (hreg i)
    refine ⟨c, hc, ?_⟩
    have e1 : (⟨e, he⟩ : M.lat ⟨centre z, h⟩) =
        ∑ i, (⟨B.repr e i, hreg i⟩ : regAt ξ ⟨centre z, h⟩) • (⟨B i, hmem i⟩ : M.lat ⟨centre z, h⟩) := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      exact (B.sum_repr e).symm
    rw [e1, map_sum]
    exact Finset.sum_congr rfl fun i _ => hsm _ _ _ (hc i)
  have hspan : ⊤ ≤ Submodule.span ℂ (Set.range b) := by
    rw [← hsp, Submodule.span_le]
    rintro _ ⟨⟨e, he⟩, rfl⟩
    obtain ⟨c, -, hc⟩ := key e he
    rw [hc]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hfin : Fintype.card (Fin r) = Module.finrank ℂ V := by
    rw [Fintype.card_fin, LieFrameIndep.finrank_eq_of_isFrameAt M h Mz B hξ hB]
  let β := basisOfTopLeSpanOfCardEqFinrank b hspan hfin
  have hβ : ∀ i, β i = b i := fun i => congrFun (coe_basisOfTopLeSpanOfCardEqFinrank b hspan hfin) i
  refine ⟨β, fun i u => ?_, fun e u hu i => ?_⟩
  · rw [hev, hβ]
    exact ⟨fun ⟨_, h⟩ => h.symm, fun h => ⟨hmem i, h.symm⟩⟩
  · obtain ⟨he, rfl⟩ := (hev e u).1 hu
    obtain ⟨c, hc, hc'⟩ := key e he
    have : β.repr (ev ⟨e, he⟩) i = c i := by
      rw [hc']
      simp only [← hβ]
      exact congrFun (β.repr_sum_self c) i
    rw [this]
    exact hc i

def Co (M : LieModel G ξ Li) (B : Fin r → Li) (z : Sp ℂ ⟶ X) (v : epsAt z ⟶ G) (c : Fin r → ℂ) : Prop :=
  ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (Mz : LieModel G z V) (b : Fin r → V),
    (∀ i, M.ValAt z (B i) (Mz.pt (b i))) ∧ v = Mz.pt (∑ i, c i • b i)

theorem exists_lin {R : Type} [CommRing R] {x : Sp R ⟶ X} {L L' : Type}
    [AddCommGroup L] [Module R L] [AddCommGroup L'] [Module R L'] (M : LieModel G x L) (M' : LieModel G x L') :
    ∃ ψ : L →ₗ[R] L', ∀ e, M'.pt (ψ e) = M.pt e := by
  choose F hF using fun e => M'.onto _ (M.tan e)
  exact ⟨{ toFun := F
           map_add' := fun a b => M'.inj (by rw [M'.add, hF, hF, hF, M.add])
           map_smul' := fun c a => M'.inj (Over.OverMorphism.ext (by
              rw [RingHom.id_apply, M'.smul, hF, hF, M.smul])) }, hF⟩

theorem co_iff (M : LieModel G ξ Li) (B : Fin r → Li) (z : Sp ℂ ⟶ X) {V : Type} [AddCommGroup V] [Module ℂ V]
    (Mz : LieModel G z V) (β : Module.Basis (Fin r) ℂ V) (hβ : ∀ i u, M.ValAt z (B i) (Mz.pt u) ↔ u = β i)
    (u : V) (c : Fin r → ℂ) : Co M B z (Mz.pt u) c ↔ c = β.repr u := by
  constructor
  · rintro ⟨V', _, _, M', b, hb, hv⟩
    obtain ⟨ψ, hψ⟩ := exists_lin M' Mz
    have h1 : ∀ i, ψ (b i) = β i := fun i => (hβ i _).1 (by rw [hψ]; exact hb i)
    have h2 : u = ∑ i, c i • β i := by
      apply Mz.inj
      rw [hv, ← hψ, map_sum]
      simp only [map_smul, h1]
    rw [h2]
    exact (β.repr_sum_self c).symm
  · rintro rfl
    exact ⟨V, inferInstance, inferInstance, Mz, β, fun i => (hβ i _).2 rfl, by rw [β.sum_repr]⟩

open Classical in

def co (M : LieModel G ξ Li) (B : Fin r → Li) (z : Sp ℂ ⟶ X) (v : epsAt z ⟶ G) : Fin r → ℂ :=
  if h : ∃ c, Co M B z v c then h.choose else 0

theorem co_eq (M : LieModel G ξ Li) (B : Fin r → Li) (z : Sp ℂ ⟶ X) {V : Type} [AddCommGroup V] [Module ℂ V]
    (Mz : LieModel G z V) (β : Module.Basis (Fin r) ℂ V) (hβ : ∀ i u, M.ValAt z (B i) (Mz.pt u) ↔ u = β i)
    (u : V) : co M B z (Mz.pt u) = β.repr u := by
  have h : ∃ c, Co M B z (Mz.pt u) c := ⟨_, (co_iff M B z Mz β hβ u _).2 rfl⟩
  rw [co, dif_pos h]
  exact (co_iff M B z Mz β hβ u _).1 h.choose_spec

theorem dual_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (φ : R →+* R') (ψ : R' →+* R'') :
    dualMap (ψ.comp φ) = (dualMap ψ).comp (dualMap φ) :=
  RingHom.ext fun a => TrivSqZeroExt.ext (by simp [dualMap]) (by simp [dualMap])

theorem extends_map (τ : ℂ →+* ℂ) (M : LieModel G ξ Li) {x x' : X} (hx : x = x') (h : genPt ξ ⤳ x)
    (h' : genPt ξ ⤳ x') (e : Li)
    (v : epsAt (X.fromSpecStalk x) ⟶ G) (hv : M.Extends ⟨x, h⟩ e v)
    (φ : X.presheaf.stalk x ⟶ CommRingCat.of ℂ) (φ' : X.presheaf.stalk x' ⟶ CommRingCat.of ℂ)
    (H : Spec.map φ' ≫ X.fromSpecStalk x' = spMap τ ≫ Spec.map φ ≫ X.fromSpecStalk x) :
    ∃ v' : epsAt (X.fromSpecStalk x') ⟶ G, M.Extends ⟨x', h'⟩ e v' ∧
      Spec.map (CommRingCat.ofHom (dualMap φ'.hom)) ≫ v'.left =
        spMap (dualMap τ) ≫ Spec.map (CommRingCat.ofHom (dualMap φ.hom)) ≫ v.left := by
  subst hx
  refine ⟨v, hv, ?_⟩
  have h1 : Spec.map φ' = Spec.map (φ ≫ CommRingCat.ofHom τ) := by
    rw [← cancel_mono (X.fromSpecStalk x), H, Spec.map_comp, Category.assoc]
  have h2 : φ' = φ ≫ CommRingCat.ofHom τ := Spec.map_injective h1
  subst h2
  have h3 : dualMap (φ ≫ CommRingCat.ofHom τ).hom = (dualMap τ).comp (dualMap φ.hom) := dual_comp _ _
  rw [h3, CommRingCat.ofHom_comp, Spec.map_comp]
  exact Category.assoc _ _ _

theorem centre_map (τ : ℂ →+* ℂ) (z : Sp ℂ ⟶ X) : centre (spMap τ ≫ z) = centre z := by
  have h : (spMap τ) (IsLocalRing.closedPoint ℂ) = IsLocalRing.closedPoint ℂ :=
    Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
  exact congrArg (fun p => z p) h

theorem valAt_map (τ : ℂ →+* ℂ) (M : LieModel G ξ Li) {z z' : Sp ℂ ⟶ X} (hz : spMap τ ≫ z = z') (e : Li)
    (w : epsAt z ⟶ G) (w' : epsAt z' ⟶ G) (hw' : w'.left = spMap (dualMap τ) ≫ w.left)
    (hw : M.ValAt z e w) : M.ValAt z' e w' := by
  subst hz
  obtain ⟨h, v, hv, hl⟩ := hw
  have hc := centre_map τ z
  have h' : genPt ξ ⤳ centre (spMap τ ≫ z) := hc ▸ h
  obtain ⟨v', hv', hl'⟩ := extends_map τ M hc.symm h h' e v hv (Scheme.stalkClosedPointTo z)
    (Scheme.stalkClosedPointTo (spMap τ ≫ z)) (by
      refine (Scheme.Spec_stalkClosedPointTo_fromSpecStalk (spMap τ ≫ z)).trans ?_
      exact congrArg (spMap τ ≫ ·) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk z).symm)
  refine ⟨h', v', hv', ?_⟩
  rw [hw', hl]
  exact hl'.symm

theorem co_map [IsCommMonObj G] (τ : ℂ →+* ℂ) (M : LieModel G ξ Li) (B : Fin r → Li) {z z' : Sp ℂ ⟶ X}
    (hz : spMap τ ≫ z = z') (v : epsAt z ⟶ G) (v' : epsAt z' ⟶ G) (hv' : v'.left = spMap (dualMap τ) ≫ v.left)
    {c : Fin r → ℂ} (h : Co M B z v c) : Co M B z' v' fun i => τ (c i) := by
  obtain ⟨V, _, _, Mz, b, hb, hv⟩ := h
  obtain ⟨V', _, _, ⟨M'⟩⟩ := lieModel_exists X G ℂ z'
  obtain ⟨j, hj, hjs, -⟩ := LieVal.exists_base τ z z' hz Mz M'
  refine ⟨V', inferInstance, inferInstance, M', fun i => j (b i),
    fun i => valAt_map τ M hz _ _ _ (hj _) (hb i), Over.OverMorphism.ext ?_⟩
  have : ∑ i, τ (c i) • j (b i) = j (∑ i, c i • b i) := by
    rw [map_sum]
    simp only [hjs]
  rw [this, hj, hv', hv]

theorem co_unique [IsCommMonObj G] [Smooth G.hom] (hξ : IsCptGen ξ) (M : LieModel G ξ Li)
    (B : Module.Basis (Fin r) Ω Li) (z : Sp ℂ ⟶ X) (h : genPt ξ ⤳ centre z)
    (hB : M.lat.IsFrameAt B ⟨centre z, h⟩) {v : epsAt z ⟶ G} {c c' : Fin r → ℂ} (h₁ : Co M B z v c)
    (h₂ : Co M B z v c') : c = c' := by
  have h₃ := h₁
  obtain ⟨V, _, _, Mz, b, -, hv⟩ := h₃
  obtain ⟨β, hβ, -⟩ := frame_basis hξ M B z h hB Mz
  rw [hv] at h₁ h₂
  exact ((co_iff M B z Mz β hβ _ _).1 h₁).trans ((co_iff M B z Mz β hβ _ _).1 h₂).symm

theorem co_conj [IsCommMonObj G] [Smooth G.hom] (hξ : IsCptGen ξ) (M : LieModel G ξ Li)
    (B : Module.Basis (Fin r) Ω Li) (z : Sp ℂ ⟶ X) (h : genPt ξ ⤳ centre (spMap (starRingEnd ℂ) ≫ z))
    (hB : M.lat.IsFrameAt B ⟨_, h⟩) (v : epsAt z ⟶ G) (v' : epsAt (spMap (starRingEnd ℂ) ≫ z) ⟶ G)
    (hv' : v'.left = spMap (dualMap (starRingEnd ℂ)) ≫ v.left) (i : Fin r) :
    co M B _ v' i = starRingEnd ℂ (co M B z v i) := by
  by_cases hc : ∃ c, Co M B z v c
  · have h1 := co_map (starRingEnd ℂ) M B rfl v v' hv' hc.choose_spec
    have hc' : ∃ c, Co M B _ v' c := ⟨_, h1⟩
    rw [co, co, dif_pos hc, dif_pos hc', co_unique hξ M B _ h hB hc'.choose_spec h1]
  · have hcc : (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ := RingHom.ext fun a => Complex.conj_conj a
    have hz : spMap (starRingEnd ℂ) ≫ spMap (starRingEnd ℂ) ≫ z = z := by
      rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hcc, CommRingCat.ofHom_id, Spec.map_id,
        Category.id_comp]
    have hd : dualMap (RingHom.id ℂ) = RingHom.id _ :=
      RingHom.ext fun a => TrivSqZeroExt.ext (by simp [dualMap]) (by simp [dualMap])
    have hv : v.left = spMap (dualMap (starRingEnd ℂ)) ≫ v'.left := by
      rw [hv', ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← dual_comp, hcc, hd,
        CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
    have hc' : ¬ ∃ c, Co M B _ v' c := fun ⟨c, h⟩ => hc ⟨_, co_map (starRingEnd ℂ) M B hz v' v hv h⟩
    rw [co, co, dif_neg hc, dif_neg hc']
    simp

theorem co_val [IsCommMonObj G] [Smooth G.hom] (hξ : IsCptGen ξ) (M : LieModel G ξ Li)
    (B : Module.Basis (Fin r) Ω Li) (z : Sp ℂ ⟶ X) (h : genPt ξ ⤳ centre z)
    (hB : M.lat.IsFrameAt B ⟨centre z, h⟩) {e : Li} {v : epsAt z ⟶ G} (hv : M.ValAt z e v) (i : Fin r) :
    ValAt ξ z (B.repr e i) (co M B z v i) := by
  obtain ⟨V, _, _, ⟨Mz⟩⟩ := lieModel_exists X G ℂ z
  obtain ⟨β, hβ, hβ'⟩ := frame_basis hξ M B z h hB Mz
  obtain ⟨h0, v₀, hv₀, hl⟩ := id hv
  obtain ⟨V₀, _, _, ⟨M₀⟩⟩ := lieModel_exists X G (X.presheaf.stalk (centre z)) (X.fromSpecStalk (centre z))
  obtain ⟨j, hj, -, -⟩ := LieVal.exists_base (A := X.presheaf.stalk (centre z)) (Scheme.stalkClosedPointTo z).hom _ z
    (LieTangent.spec_centre z) M₀ Mz
  obtain ⟨u₀, hu₀⟩ := M₀.onto v₀ hv₀.1
  have hu : v = Mz.pt (j u₀) := Over.OverMorphism.ext (by rw [hj, hu₀, hl])
  rw [hu] at hv ⊢
  rw [co_eq M B z Mz β hβ]
  exact hβ' e _ hv i

theorem exists_core {V : Type} [AddCommGroup V] [Module ℂ V] {Λ : Type} [Fintype Λ] (ρ : Λ → ℝ) (hρ : ∀ l, 0 ≤ ρ l)
    (f : Λ → V →ₗ[ℂ] (Fin r → ℂ)) (l₀ : Λ) (h₀ : 0 < ρ l₀) (hf : Function.Injective (f l₀)) :
    ∃ core : InnerProductSpace.Core ℂ V,
      ∀ a b, core.inner a b = ∑ l, (ρ l : ℂ) * ∑ i, starRingEnd ℂ (f l a i) * f l b i := by
  have hre : ∀ a, ∑ l, (ρ l : ℂ) * ∑ i, starRingEnd ℂ (f l a i) * f l a i =
      ((∑ l, ρ l * ∑ i, Complex.normSq (f l a i) : ℝ) : ℂ) := by
    intro a
    push_cast
    simp only [Complex.normSq_eq_conj_mul_self]
  have hnn : ∀ a l, 0 ≤ ρ l * ∑ i, Complex.normSq (f l a i) := fun a l =>
    mul_nonneg (hρ l) (Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _)
  refine ⟨{ inner := fun a b => ∑ l, (ρ l : ℂ) * ∑ i, starRingEnd ℂ (f l a i) * f l b i
            conj_inner_symm := fun a b => ?_
            re_inner_nonneg := fun a => ?_
            add_left := fun a b c => ?_
            smul_left := fun a b c => ?_
            definite := fun a ha => ?_ }, fun _ _ => rfl⟩
  · simp only [map_sum, map_mul, Complex.conj_ofReal, Complex.conj_conj, mul_comm]
  · show 0 ≤ (∑ l, (ρ l : ℂ) * ∑ i, starRingEnd ℂ (f l a i) * f l a i).re
    rw [hre, Complex.ofReal_re]
    exact Finset.sum_nonneg fun l _ => hnn a l
  · simp only [map_add, Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]
  · simp only [map_smul, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => by ring
  · have h1 : (∑ l, (ρ l : ℂ) * ∑ i, starRingEnd ℂ (f l a i) * f l a i) = 0 := ha
    rw [hre, Complex.ofReal_eq_zero, Finset.sum_eq_zero_iff_of_nonneg fun l _ => hnn a l] at h1
    have h2 := (mul_eq_zero.1 (h1 l₀ (Finset.mem_univ _))).resolve_left h₀.ne'
    rw [Finset.sum_eq_zero_iff_of_nonneg fun i _ => Complex.normSq_nonneg _] at h2
    apply hf
    rw [map_zero]
    funext i
    exact Complex.normSq_eq_zero.1 (h2 i (Finset.mem_univ _))

end CoverDenseAlt.Met
