import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmpNaturality
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JointlyEpiSectionsGenerateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratingSectionsProjectiveMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveMapUniqueOfRelationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveRelationPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveRelationUniqueQuotientStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveMapUniversalLineStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingLocusClosedSubschemeStatement

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.LineQuot

namespace GlobalTheory.Vert.Flag

variable {X : Scheme.{0}} {E K : X.Modules} {r : ℕ}

theorem exists_extend {i : K ⟶ E} (hi : IsSubbundle i) (hE : IsVB E (r + 1)) (fl : Vert.Flag K r) :
    ∃ fl' : Vert.Flag E (r + 1), ∀ j : Fin (r + 1),
      ∃ e : fl'.F j.castSucc ≅ fl.F j, e.hom ≫ fl.ι j ≫ i = fl'.ι j.castSucc := by
  let G : Fin (r + 2) → Σ A : X.Modules, (A ⟶ E) :=
    fun j => Fin.lastCases (motive := fun _ => Σ A : X.Modules, (A ⟶ E)) ⟨E, 𝟙 E⟩
      (fun k => ⟨fl.F k, fl.ι k ≫ i⟩) j
  have hlast : G (Fin.last (r + 1)) = ⟨E, 𝟙 E⟩ := Fin.lastCases_last ..
  have hcast (k : Fin (r + 1)) : G k.castSucc = ⟨fl.F k, fl.ι k ≫ i⟩ := Fin.lastCases_castSucc ..
  have hsub (j : Fin (r + 2)) : IsSubbundle (G j).2 := by
    induction j using Fin.lastCases with
    | last => rw [hlast]; exact VB.isSubbundle_of_isIso _
    | cast k => rw [hcast]; exact isSubbundle_ι_comp hi fl k
  have hvb (j : Fin (r + 2)) : IsVB (G j).1 j := by
    induction j using Fin.lastCases with
    | last => rw [hlast]; exact hE
    | cast k => rw [hcast]; exact fl.isVB k
  have hstep (k : Fin (r + 1)) :
      ∃ f : (G k.castSucc).1 ⟶ (G k.succ).1, f ≫ (G k.succ).2 = (G k.castSucc).2 := by
    induction k using Fin.lastCases with
    | last =>
      rw [Fin.succ_last, hlast, hcast]
      exact ⟨fl.ι _ ≫ i, Category.comp_id _⟩
    | cast k =>
      rw [← Fin.castSucc_succ, hcast, hcast]
      exact ⟨fl.step k, fl.step_ι_assoc k i⟩
  choose step step_ι using hstep
  have hiso : IsIso (G (Fin.last (r + 1))).2 := by
    rw [hlast]; exact IsIso.id E
  refine ⟨⟨fun j => (G j).1, fun j => (G j).2, hsub, hvb, step, step_ι, hiso⟩, fun j => ?_⟩
  change ∃ e : (G j.castSucc).1 ≅ fl.F j, e.hom ≫ fl.ι j ≫ i = (G j.castSucc).2
  rw [hcast]
  exact ⟨Iso.refl _, Category.id_comp _⟩

theorem exists_comp_ι_of_le (fl : Vert.Flag E r) {i j : Fin (r + 1)} (h : i ≤ j) :
    ∃ t : fl.F i ⟶ fl.F j, t ≫ fl.ι j = fl.ι i := by
  induction j using Fin.induction with
  | zero => obtain rfl := Fin.le_zero_iff.1 h; exact ⟨𝟙 _, Category.id_comp _⟩
  | succ j ih =>
    obtain rfl | h' := h.eq_or_lt
    · exact ⟨𝟙 _, Category.id_comp _⟩
    · obtain ⟨t, ht⟩ := ih (Fin.le_castSucc_iff.2 h')
      exact ⟨t ≫ fl.step j, by rw [Category.assoc, fl.step_ι, ht]⟩

theorem exists_trunc {i : K ⟶ E} (fl' : Vert.Flag E (r + 1)) (a : K ≅ fl'.F (Fin.last r).castSucc)
    (ha : a.hom ≫ fl'.ι (Fin.last r).castSucc = i) : ∃ fl : Vert.Flag K r, ∀ j : Fin (r + 1),
      ∃ e : fl.F j ≅ fl'.F j.castSucc, e.hom ≫ fl'.ι j.castSucc = fl.ι j ≫ i := by
  subst ha
  choose t ht using fun j : Fin (r + 1) =>
    fl'.exists_comp_ι_of_le (Fin.castSucc_le_castSucc_iff.2 (Fin.le_last j))
  have hm (j : Fin (r + 1)) : Mono (t j) := mono_of_mono_fac (ht j)
  have hl : t (Fin.last r) = 𝟙 _ := by rw [← cancel_mono (fl'.ι _), ht, Category.id_comp]
  have hs (j : Fin (r + 1)) : IsSubbundle (t j) := by
    refine ⟨hm j, r - j, VB.isVB_X₁_of_shortExact X _ (r - j) _
      (shortExact_cokernel_comp (t j) (fl'.ι (Fin.last r).castSucc)) ?_ (fl'.isVB_cokernel _)⟩
    have h := (fl'.isVB_cokernel j.castSucc).of_iso (cokernelIsoOfEq (ht j).symm)
    rwa [show r + 1 - (j.castSucc : ℕ) = r - j + (r + 1 - ((Fin.last r).castSucc : ℕ)) by
      have := j.2; simp; omega] at h
  let fl : Vert.Flag (fl'.F (Fin.last r).castSucc) r :=
    ⟨fun j => fl'.F j.castSucc, t, hs, fun j => fl'.isVB j.castSucc, fun j => fl'.step j.castSucc, fun j => by
      rw [← cancel_mono (fl'.ι _), Category.assoc, ht, ht]; exact fl'.step_ι j.castSucc,
      by rw [hl]; exact IsIso.id _⟩
  refine ⟨fl.ofIso a.symm, fun j => ⟨Iso.refl _, ?_⟩⟩
  change 𝟙 _ ≫ _ = (t j ≫ a.inv) ≫ _
  simp [ht]

end GlobalTheory.Vert.Flag

namespace GlobalTheory.LineQuot

section Rel

variable {T : Scheme.{0}} {R : Type} [CommRing R] {N : ℕ} {L L' Q Q' : T.Modules} {φ : T ⟶ PSpace R N}
  {s : Fin (N + 1) → (L ⟶ Q)}

theorem Rel.pre (h : Rel φ s) (a : L' ⟶ L) : Rel φ fun j => a ≫ s j :=
  fun i j W hW t => h i j W hW (a.app W t)

theorem Rel.post (h : Rel φ s) (a : Q ⟶ Q') : Rel φ fun j => s j ≫ a := fun i j W hW t =>
  (congrArg (a.app W) (h i j W hW t)).trans (Scheme.Modules.Hom.app_smul ..)

end Rel

theorem map_biproduct_ext {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D] (Φ : C ⥤ D)
    [Φ.Additive] {ι : Type} [Fintype ι] (f : ι → C) [HasBiproduct f] {Z : D} {a b : Φ.obj (⨁ f) ⟶ Z}
    (h : ∀ j, Φ.map (biproduct.ι f j) ≫ a = Φ.map (biproduct.ι f j) ≫ b) : a = b := by
  have e (c : Φ.obj (⨁ f) ⟶ Z) : c = ∑ j, Φ.map (biproduct.π f j) ≫ Φ.map (biproduct.ι f j) ≫ c := by
    simp only [← Functor.map_comp_assoc, ← Preadditive.sum_comp, ← Functor.map_sum, biproduct.total, Φ.map_id,
      Category.id_comp]
  rw [e a, e b]
  simp only [h]

theorem exists_isLineQuot_sum {k : Type} [CommRing k] {B : Scheme.{0}} (q : B ⟶ Sp k) (N : ℕ) {L : B.Modules}
    (hL : IsVB L 1) [HasBiproduct fun _ : Fin (N + 1) => L] :
    ∃ (Q : (pullback q (PSpace.str k N)).Modules) (p : _ ⟶ Q),
      IsLineQuot (pullback.fst q (PSpace.str k N)) (⨁ fun _ : Fin (N + 1) => L) p := by
  classical
  set π := pullback.fst q (PSpace.str k N) with hπ
  set φ₀ := pullback.snd q (PSpace.str k N) with hφ₀
  obtain ⟨Q, s, hQ, hs, hr⟩ := GlobalTheory.T.projective_map_universal_line k N _ φ₀ _ (hL.pullback π)
  let u (j : Fin (N + 1)) : L ⟶ ⨁ fun _ : Fin (N + 1) => L := biproduct.ι (fun _ : Fin (N + 1) => L) j
  obtain ⟨p, hp⟩ : ∃ p : (Scheme.Modules.pullback π).obj (⨁ fun _ : Fin (N + 1) => L) ⟶ Q,
      ∀ j, (Scheme.Modules.pullback π).map (u j) ≫ p = s j :=
    ⟨∑ j, (Scheme.Modules.pullback π).map (biproduct.π _ j) ≫ s j, fun j => by
      simp only [u, Preadditive.comp_sum, ← Functor.map_comp_assoc]
      rw [Finset.sum_eq_single j (fun i _ hi => by rw [biproduct.ι_π_ne _ hi.symm]; simp) (by simp)]
      simp⟩
  have hepi : Epi p := (Preadditive.epi_iff_cancel_zero _).2 fun Z a ha => hs Z a fun j => by
    rw [← hp, Category.assoc, ha, comp_zero]
  refine ⟨Q, p, hQ, hepi, fun T g Q' p' hQ' hp' => ?_⟩
  let s' (j : Fin (N + 1)) := (Scheme.Modules.pullback g).map (u j) ≫ p'
  have hs' : Gen s' := GlobalTheory.T.jointly_epi_sections_generate T _ _ N s' (hL.pullback g) hQ' fun Z a ha => by
    rw [← cancel_epi p']
    exact map_biproduct_ext _ _ fun j => by simpa [s', u] using ha j
  have key (g' : T ⟶ pullback q (PSpace.str k N)) (w : g' ≫ π = g) (e : (Scheme.Modules.pullback g').obj Q ⟶ Q') :
      (Scheme.Modules.pullback g').map p ≫ e = (cmp g' π w).hom.app _ ≫ p' ↔
        ∀ j, (Scheme.Modules.pullback g').map (s j) ≫ e = (cmp g' π w).hom.app _ ≫ s' j := by
    have H (j) : (Scheme.Modules.pullback g').map ((Scheme.Modules.pullback π).map (u j)) ≫
        (Scheme.Modules.pullback g').map p ≫ e = (Scheme.Modules.pullback g').map (s j) ≫ e := by
      rw [← Functor.map_comp_assoc, hp]
    refine ⟨fun h j => by rw [← H, h, cmp_naturality_assoc], fun h =>
      map_biproduct_ext (Scheme.Modules.pullback π ⋙ Scheme.Modules.pullback g') _ fun j => ?_⟩
    exact (H j).trans ((h j).trans (cmp_naturality_assoc g' π w (u j) p').symm)
  obtain ⟨φ, hφ, hφr⟩ := GlobalTheory.T.generating_sections_projective_map k N T (g ≫ q) _ _ s' (hL.pullback g) hQ' hs'
  have w : pullback.lift g φ hφ.symm ≫ π = g := pullback.lift_fst ..
  have w' : pullback.lift g φ hφ.symm ≫ φ₀ = φ := pullback.lift_snd ..
  refine ⟨pullback.lift g φ hφ.symm, ⟨w, ?_⟩, ?_⟩
  · generalize pullback.lift g φ hφ.symm = g' at w w'
    have hj : JointEpi fun j => (Scheme.Modules.pullback g').map (s j) := fun Z a ha => by
      rw [← cancel_epi ((Scheme.Modules.pullback g').map p)]
      refine map_biproduct_ext (Scheme.Modules.pullback π ⋙ Scheme.Modules.pullback g') _ fun j => ?_
      have := ha j
      dsimp only at this
      rw [← hp, Functor.map_comp, Category.assoc] at this
      exact this.trans (by simp)
    have h₁ := (hL.pullback π).pullback g'
    obtain ⟨e, he⟩ := GlobalTheory.T.projective_relation_unique_quotient k N T _ _ Q' _ _ φ h₁ (hQ.pullback g') hj (GlobalTheory.T.jointly_epi_sections_generate T _ _ N _ h₁ (hQ.pullback g') hj)
      (w' ▸ GlobalTheory.T.projective_relation_pullback k N _ _ g' _ _ s φ₀ (hL.pullback π) hQ hr) (hφr.pre ((cmp g' π w).hom.app L))
    exact ⟨e, (key g' w e).2 he⟩
  · rintro g' ⟨w₁, e, he⟩
    have h₁ := ((GlobalTheory.T.projective_relation_pullback k N _ _ g' _ _ s φ₀ (hL.pullback π) hQ hr).post e).pre ((cmp g' π w₁).inv.app L)
    simp only [(key g' w₁ e).1 he, Iso.inv_hom_id_app_assoc] at h₁
    refine pullback.hom_ext (w₁.trans w.symm) (Eq.trans ?_ w'.symm)
    refine GlobalTheory.T.projective_map_unique_of_relation k N T _ _ s' _ _ (hL.pullback g) hQ' hs' ?_ h₁ hφr
    rw [hφ, Category.assoc, ← pullback.condition, ← Category.assoc, w₁]

theorem IsLineQuot.exists_closed {Y B : Scheme.{0}} {π : Y ⟶ B} {F E : B.Modules} [F.IsQuasicoherent]
    [E.IsQuasicoherent] {Q : Y.Modules} {p : (Scheme.Modules.pullback π).obj F ⟶ Q} (h : IsLineQuot π F p)
    (a : F ⟶ E) [Epi a] : ∃ (Z : Scheme.{0}) (j : Z ⟶ Y) (Q₁ : Z.Modules) (p₁ : _ ⟶ Q₁),
      IsClosedImmersion j ∧ IsLineQuot (j ≫ π) E p₁ := by
  obtain ⟨hQ, hp, H⟩ := h
  obtain ⟨Z, j, hj, hZ⟩ := GlobalTheory.T.vanishing_locus_closed_subscheme Y _ Q ((Scheme.Modules.pullback π).map (kernel.ι a) ≫ p) inferInstance hQ
  have hex := (ShortComplex.exact_kernel a).map_of_epi_of_preservesCokernel (Scheme.Modules.pullback (j ≫ π))
    (inferInstanceAs (Epi a)) inferInstance
  have : Epi ((ShortComplex.mk (kernel.ι a) a (kernel.condition a)).map (Scheme.Modules.pullback (j ≫ π))).g :=
    inferInstanceAs (Epi ((Scheme.Modules.pullback (j ≫ π)).map a))
  obtain ⟨p₁, hp₁⟩ : ∃ p₁ : (Scheme.Modules.pullback (j ≫ π)).obj E ⟶ (Scheme.Modules.pullback j).obj Q,
      (Scheme.Modules.pullback (j ≫ π)).map a ≫ p₁ =
        (cmp j π rfl).inv.app F ≫ (Scheme.Modules.pullback j).map p := hex.desc' _ (by
    have := (hZ Z j).2 ⟨𝟙 _, Category.id_comp _⟩
    change (Scheme.Modules.pullback (j ≫ π)).map (kernel.ι a) ≫ _ = _
    rw [← cancel_epi ((cmp j π rfl).hom.app (kernel a)), ← cmp_naturality_assoc, Iso.hom_inv_id_app_assoc,
      ← Functor.map_comp, this, comp_zero])
  refine ⟨Z, j, _, p₁, hj, hQ.pullback j, epi_of_epi_fac hp₁, fun T g Q' p' hQ' hp' => ?_⟩
  have key (h : T ⟶ Z) (g₁ : T ⟶ Y) (w₀ : h ≫ j = g₁) (w₁ : g₁ ≫ π = g) (w : h ≫ j ≫ π = g)
      (e₁ : (Scheme.Modules.pullback g₁).obj Q ⟶ Q') :
      (Scheme.Modules.pullback h).map p₁ ≫ (cmp h j w₀).hom.app Q ≫ e₁ = (cmp h (j ≫ π) w).hom.app E ≫ p' ↔
        (Scheme.Modules.pullback g₁).map p ≫ e₁ =
          (cmp g₁ π w₁).hom.app F ≫ (Scheme.Modules.pullback g).map a ≫ p' := by
    rw [← cancel_epi ((Scheme.Modules.pullback h).map ((Scheme.Modules.pullback (j ≫ π)).map a)),
      ← Functor.map_comp_assoc, hp₁, cmp_naturality_assoc,
      ← cancel_epi ((Scheme.Modules.pullback h).map ((cmp j π rfl).hom.app F)), ← Functor.map_comp_assoc,
      Iso.hom_inv_id_app_assoc, cmp_naturality_assoc, cmp_assoc_assoc h j π rfl w w₀ w₁, cancel_epi]
  obtain ⟨g₁, ⟨w₁, e₁, he₁⟩, hu⟩ := H T g Q' ((Scheme.Modules.pullback g).map a ≫ p') hQ' inferInstance
  have : Epi e₁ := epi_of_epi_fac he₁
  have := SameLine.isIso_of_epi e₁ (hQ.pullback g₁) hQ'
  obtain ⟨h, w₀⟩ := (hZ T g₁).1 (by
    rw [← cancel_mono e₁, Functor.map_comp, Category.assoc, he₁, cmp_naturality_assoc, ← Functor.map_comp_assoc,
      kernel.condition]
    simp)
  have w : h ≫ j ≫ π = g := by rw [← Category.assoc, w₀, w₁]
  refine ⟨h, ⟨w, _, (key h g₁ w₀ w₁ w e₁).2 he₁⟩, ?_⟩
  rintro h' ⟨w', e', he'⟩
  rw [← cancel_mono j, w₀]
  exact hu _ ⟨(Category.assoc ..).trans w', (cmp h' j rfl).inv.app Q ≫ e', (key h' _ rfl _ w' _).1 (by simpa using he')⟩

theorem exists_isLineQuot_isProjOver {k : Type} [CommRing k] {B : Scheme.{0}} {q : B ⟶ Sp k} (hq : IsProjOver q)
    {E : B.Modules} {r : ℕ} (hE : IsVB E r) : ∃ (Y : Scheme.{0}) (π : Y ⟶ B) (Q : Y.Modules) (p : _ ⟶ Q),
      IsLineQuot π E p ∧ IsProjOver (π ≫ q) := by
  have := hE.isFiniteQC
  have := hE.isQuasicoherent
  have := Abelian.hasFiniteBiproducts (C := B.Modules)
  obtain ⟨-, A, hA⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hq
  obtain ⟨n, N, φ, hφ⟩ := (hA.eventually_exists_epi_sigma E).exists
  have hL := isVB_toMod (Twist.isLB_lbZPow hA.isLB (-n))
  generalize LB.toMod (lbZPow A (-n)) = L at φ hφ hL
  have := hL.isQuasicoherent
  let a : (⨁ fun _ : Fin (N + 1) => L) ⟶ E := biproduct.desc (Fin.cons 0 fun j => Sigma.ι (fun _ => L) j ≫ φ)
  have : Epi a := (Preadditive.epi_iff_cancel_zero _).2 fun Z b hb => by
    rw [← cancel_epi φ]
    refine Sigma.hom_ext _ _ fun j => ?_
    simpa [a] using biproduct.ι _ j.succ ≫= hb
  obtain ⟨Q, p, h⟩ := exists_isLineQuot_sum q N hL
  obtain ⟨Z, j, Q₁, p₁, hj, h₁⟩ := h.exists_closed a
  refine ⟨Z, _, Q₁, p₁, h₁, ?_⟩
  rw [Category.assoc]
  exact ProjSpace.isProjOver_comp_of_isClosedImmersion j
    (ProjSpace.isProjOver_pullback hq ⟨N, 𝟙 _, inferInstance, Category.id_comp _⟩)

end GlobalTheory.LineQuot

namespace GlobalTheory.LineQuot

open GlobalTheory.CovTest

theorem isVB_kernel {X : Scheme.{0}} {E Q : X.Modules} {r : ℕ} (hE : IsVB E (r + 1)) (hQ : IsVB Q 1) (p : E ⟶ Q)
    [Epi p] : IsVB (kernel p) r :=
  isVB_X₁_of_shortExact X (.mk (kernel.ι p) p (kernel.condition p)) r 1 { exact := ShortComplex.exact_kernel p } hE hQ

theorem IsLineQuot.tower {B Y₁ Y₂ : Scheme.{0}} {π₁ : Y₁ ⟶ B} {E : B.Modules} {r : ℕ} (hE : IsVB E (r + 1))
    {Q : Y₁.Modules} {p : (Scheme.Modules.pullback π₁).obj E ⟶ Q} (h : IsLineQuot π₁ E p) {π₂ : Y₂ ⟶ Y₁}
    {fl : Unit → Vert.Flag ((Scheme.Modules.pullback π₂).obj (kernel p)) r}
    (h₂ : IsFlagBundle π₂ (fun _ : Unit => kernel p) (fun _ => r) fl) :
    ∃ fl₂, IsFlagBundle (π₂ ≫ π₁) (fun _ : Unit => E) (fun _ => r + 1) fl₂ := by
  obtain ⟨hQ, hp, H⟩ := h
  have hH := isVB_kernel (hE.pullback π₁) hQ p
  have hι : IsSubbundle (kernel.ι p) := isSubbundle_of_shortExact
    (S := .mk (kernel.ι p) p (kernel.condition p)) { exact := ShortComplex.exact_kernel p } hQ
  have hsub {T : Scheme.{0}} (g₁ : T ⟶ Y₁) := SubPull.isSubbundle_pullback _ _ g₁ _ _ _ r hH hι
  have hex {T : Scheme.{0}} (g₁ : T ⟶ Y₁) := (ShortComplex.exact_kernel p).map_of_epi_of_preservesCokernel
    (Scheme.Modules.pullback g₁) hp inferInstance
  obtain ⟨fl₁, hfl₁⟩ := Vert.Flag.exists_extend (hsub π₂) ((hE.pullback π₁).pullback π₂) (fl ())
  choose e₀ he₀ using hfl₁
  refine ⟨fun _ => fl₁.ofIso ((cmp π₂ π₁ rfl).app E), fun T g fl' => ?_⟩
  have hB (g' : T ⟶ Y₂) (g₁ : T ⟶ Y₁) (w₂ : g' ≫ π₂ = g₁) (w₁ : g₁ ≫ π₁ = g) (w : g' ≫ π₂ ≫ π₁ = g) (j : Fin (r + 1)) :
      (Scheme.Modules.pullback g').map (fl₁.ι j.castSucc ≫ (cmp π₂ π₁ rfl).hom.app E) ≫
        (cmp g' (π₂ ≫ π₁) w).hom.app E = (Scheme.Modules.pullback g').map (e₀ j).hom ≫
          ((Scheme.Modules.pullback g').map ((fl ()).ι j) ≫ (cmp g' π₂ w₂).hom.app _) ≫
            (Scheme.Modules.pullback g₁).map (kernel.ι p) ≫ (cmp g₁ π₁ w₁).hom.app E := by
    rw [← he₀]
    simp only [Functor.map_comp, Category.assoc]
    rw [cmp_assoc g' π₂ π₁ rfl w w₂ w₁, cmp_naturality_assoc]
  set i' := (fl' ()).ι (Fin.last r).castSucc with hi'
  have hQ' : IsVB (cokernel i') 1 := by simpa using (fl' ()).isVB_cokernel (Fin.last r).castSucc
  obtain ⟨g₁, ⟨w₁, e, he⟩, hu⟩ := H T g _ (cokernel.π i') hQ' inferInstance
  have : Epi e := epi_of_epi_fac he
  have := SameLine.isIso_of_epi e (hQ.pullback g₁) hQ'
  have := (hsub g₁).mono
  have : Mono ((ShortComplex.mk (kernel.ι p) p (kernel.condition p)).map (Scheme.Modules.pullback g₁)).f := this
  obtain ⟨a, ha⟩ : ∃ a, a ≫ i' = (Scheme.Modules.pullback g₁).map (kernel.ι p) ≫ (cmp g₁ π₁ w₁).hom.app E :=
    (ShortComplex.exact_cokernel i').lift' _ (by
      rw [Category.assoc, ← he, ← Functor.map_comp_assoc, kernel.condition]; simp)
  obtain ⟨b, hb⟩ : ∃ b, b ≫ (Scheme.Modules.pullback g₁).map (kernel.ι p) = i' ≫ (cmp g₁ π₁ w₁).inv.app E :=
    (hex g₁).lift' _ (by
      change _ ≫ (Scheme.Modules.pullback g₁).map p = 0
      rw [← cancel_mono e, Category.assoc, Category.assoc, he]; simp)
  obtain ⟨fl'', hfl''⟩ := Vert.Flag.exists_trunc (fl' ())
    ⟨a, b, by rw [← cancel_mono ((Scheme.Modules.pullback g₁).map (kernel.ι p)), Category.assoc, hb,
      reassoc_of% ha]; simp, by rw [← cancel_mono i', Category.assoc, ha, reassoc_of% hb]; simp⟩ ha
  choose ε hε using hfl''
  obtain ⟨g', ⟨w₂, hδ⟩, hu₂⟩ := h₂ T g₁ fun _ => fl''
  have w : g' ≫ π₂ ≫ π₁ = g := by rw [← Category.assoc, w₂, w₁]
  refine ⟨g', ⟨w, fun _ i => ?_⟩, ?_⟩
  · induction i using Fin.lastCases with
    | last =>
      exact ⟨asIso ((Scheme.Modules.pullback g').map ((fl₁.ofIso ((cmp π₂ π₁ rfl).app E)).ι (Fin.last _)) ≫
        (cmp g' (π₂ ≫ π₁) w).hom.app E) ≪≫ (asIso ((fl' ()).ι (Fin.last _))).symm, by simp [cmp_hom_app]⟩
    | cast j =>
      obtain ⟨δ, hδ⟩ := hδ () j
      refine ⟨(Scheme.Modules.pullback g').mapIso (e₀ j) ≪≫ δ ≪≫ ε j, Eq.trans ?_ (hB g' g₁ w₂ w₁ w j).symm⟩
      rw [cmp_hom_app, ← hδ]
      simp [hε]
  · rintro g'' ⟨w', hη⟩
    have w₂' : g'' ≫ π₂ = g₁ := by
      obtain ⟨η, hη⟩ := hη () (Fin.last r).castSucc
      have w₁' := (Category.assoc ..).trans w'
      have hz := hη.trans (hB g'' _ rfl w₁' w' (Fin.last r))
      have : Epi ((ShortComplex.mk (kernel.ι p) p (kernel.condition p)).map (Scheme.Modules.pullback (g'' ≫ π₂))).g :=
        inferInstanceAs (Epi ((Scheme.Modules.pullback (g'' ≫ π₂)).map p))
      refine hu _ ⟨w₁', (hex (g'' ≫ π₂)).desc' _ ?_⟩
      change (Scheme.Modules.pullback (g'' ≫ π₂)).map (kernel.ι p) ≫ _ = 0
      rw [← cancel_epi ((Scheme.Modules.pullback g'').map ((fl ()).ι (Fin.last r)) ≫ (cmp g'' π₂ rfl).hom.app _),
        ← cancel_epi ((Scheme.Modules.pullback g'').map (e₀ (Fin.last r)).hom), Category.assoc, ← reassoc_of% hz, ← hi']
      simp
    refine hu₂ _ ⟨w₂', fun _ j => ?_⟩
    obtain ⟨η, hη⟩ := hη () j.castSucc
    have hz := hη.trans (hB g'' _ w₂' w₁ w' j)
    refine ⟨((Scheme.Modules.pullback g'').mapIso (e₀ j)).symm ≪≫ η ≪≫ (ε j).symm, ?_⟩
    rw [← cancel_mono ((Scheme.Modules.pullback g₁).map (kernel.ι p) ≫ (cmp g₁ π₁ w₁).hom.app E),
      ← cancel_epi ((Scheme.Modules.pullback g'').map (e₀ j).hom), ← cmp_hom_app, ← hz, Category.assoc, ← hε]
    simp [← Functor.map_comp_assoc]

open ZeroObject in

theorem exists_isFlagBundle_isProjOver : ∀ (k : Type) [CommRing k] [IsNoetherianRing k] (B : Scheme.{0}) (q : B ⟶ Sp k) (E : B.Modules) (r : ℕ), IsProjOver q → GlobalTheory.VB.IsVB E r → ∃ (Y : Scheme.{0}) (π : Y ⟶ B) (fl : ∀ _ : Unit, GlobalTheory.Vert.Flag ((Scheme.Modules.pullback π).obj E) r), GlobalTheory.CovTest.IsFlagBundle π (fun _ : Unit => E) (fun _ => r) fl ∧ IsProjOver (π ≫ q) := by
  intro k _ _ B q E r hq hE
  induction r generalizing B with
  | zero =>
    have h := hE.pullback (𝟙 B)
    refine ⟨B, 𝟙 B, fun _ => ⟨fun _ => _, fun _ => 𝟙 _, fun _ => isSubbundle_of_isIso _, fun i => by simpa using h,
      finZeroElim, finZeroElim, inferInstance⟩, fun T g fl' => ⟨g, ⟨Category.comp_id g, fun a i => ?_⟩,
        fun _ ⟨w, _⟩ => (Category.comp_id _).symm.trans w⟩, by rwa [Category.id_comp]⟩
    have z := isVB_zero_iff.1 (h.pullback g)
    exact ⟨z.iso (isVB_zero_iff.1 (by simpa using (fl' a).isVB i)), z.eq_of_src _ _⟩
  | succ r ih =>
    obtain ⟨Y₁, π₁, Q, p, h, h₁⟩ := exists_isLineQuot_isProjOver hq hE
    have := h.2.1
    obtain ⟨Y₂, π₂, fl, h₂, h₃⟩ := ih Y₁ (π₁ ≫ q) _ h₁ (isVB_kernel (hE.pullback π₁) h.1 p)
    obtain ⟨fl₂, h₄⟩ := h.tower hE h₂
    exact ⟨Y₂, _, fl₂, h₄, by rwa [Category.assoc]⟩

end GlobalTheory.LineQuot

end
