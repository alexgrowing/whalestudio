import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GalLab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueHomExtensionOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoOfGenericNormalLocalBase
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.FiniteDimensionalBase
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecializesIsLocalization
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.GalTrans

open GlobalTheory.CechPic

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] {f : A →+* B} {g : B →+* C} {h : A →+* C}
    (e : g.comp f = h) : spMap g ≫ spMap f = spMap h := by
  subst e
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem iso_iff {X Y : Scheme.{0}} {L : LB X} {M : LB Y} (hL : L.IsLB) (hM : M.IsLB) (φ : X ⟶ Y) :
    LBIso L (M.pull φ) ↔ cls L hL = pull φ (cls M hM) := by
  rw [← cls_pull hM φ (pull_isLB hM φ)]
  exact (cls_eq_iff hL _).symm

theorem exists_factor {S S' S'' : Scheme.{0}} (P : PolAV S) (P' : PolAV S') (P'' : PolAV S'') {f : S' ⟶ S} {g : S'' ⟶ S'}
    {h : S'' ⟶ S} (e : g ≫ f = h) {φ : P'.A.left ⟶ P.A.left} {ψ : P''.A.left ⟶ P.A.left}
    (hφ : IsGrpPullback P'.A P.A f φ) (hψ : IsGrpPullback P''.A P.A h ψ) (lφ : LBIso P'.L (P.L.pull φ))
    (lψ : LBIso P''.L (P.L.pull ψ)) :
    ∃ j : P''.A.left ⟶ P'.A.left, IsGrpPullback P''.A P'.A g j ∧ LBIso P''.L (P'.L.pull j) ∧ j ≫ φ = ψ := by
  subst e
  have w : ψ ≫ P.A.hom = (P''.A.hom ≫ g) ≫ f := by rw [hψ.1.w, Category.assoc]
  have k := hφ.1.lift_fst _ _ w
  refine ⟨hφ.1.lift _ _ w, hφ.cancel (hψ.congr rfl k.symm) (hφ.1.lift_snd _ _ w), ?_, k⟩
  rw [iso_iff P''.isLB P'.isLB, (iso_iff P'.isLB P.isLB _).1 lφ, ← pull_comp, k]
  exact (iso_iff P''.isLB P.isLB _).1 lψ

theorem lb_comp {X Y Z : Scheme.{0}} {L : LB X} {M : LB Y} {N : LB Z} (hL : L.IsLB) (hM : M.IsLB) (hN : N.IsLB)
    {φ : X ⟶ Y} {ψ : Y ⟶ Z} (h₁ : LBIso L (M.pull φ)) (h₂ : LBIso M (N.pull ψ)) : LBIso L (N.pull (φ ≫ ψ)) := by
  rw [iso_iff hL hN, pull_comp, ← (iso_iff hM hN _).1 h₂]
  exact (iso_iff hL hM _).1 h₁

theorem exists_iso {O Ω : Type} [CommRing O] [IsDomain O] [IsLocalRing O] [IsNoetherianRing O] [IsIntegrallyClosed O]
    [Field Ω] [Algebra O Ω] [IsFractionRing O Ω] (B B' : PolAV (Sp O)) (Q : PolAV (Sp Ω))
    {j : Q.A.left ⟶ B.A.left} {j' : Q.A.left ⟶ B'.A.left} (hj : IsGrpPullback Q.A B.A (spMap (algebraMap O Ω)) j)
    (hj' : IsGrpPullback Q.A B'.A (spMap (algebraMap O Ω)) j') (l : LBIso Q.L (B.L.pull j))
    (l' : LBIso Q.L (B'.L.pull j')) :
    ∃ E : B.A.left ⟶ B'.A.left, IsGrpPullback B.A B'.A (𝟙 _) E ∧ LBIso B.L (B'.L.pull E) ∧ j ≫ E = j' := by
  have hg : GlobalTheory.IsGenericPointHom (S := Sp O) (spMap (algebraMap O Ω)) := .fractionField O Ω
  have hn := GlobalTheory.Published.SemiAbelianHomExtension.isNormalScheme_spec O
  obtain ⟨E, ⟨hm, hE⟩, -⟩ := GlobalTheory.semiAbelianHomExtension_holds.generic_existsUnique_iso_of_extensions
    (GlobalTheory.IsNormalScheme.pred _) hg (GlobalTheory.isSemiAbelian_of_isAbelianScheme _ B.isAb)
    (GlobalTheory.isSemiAbelian_of_isAbelianScheme _ B'.isAb) hj hj'
  refine ⟨E.hom.left, isGrpPullback_of_iso E, ?_, hE⟩
  have := B.isAb.smooth
  have := B.isAb.geomConnected
  have : GeometricallyIntegral B.A.hom := GlobalTheory.geometricallyIntegral_of_smooth _
  refine GlobalTheory.Mum.lbIso_of_generic_local O B.A (eSec B.A) (Over.w (MonObj.one (X := B.A))) _ _ B.isLB (pull_isLB B'.isLB _) ?_
  let e : Ω →+* FractionRing O := (FractionRing.algEquiv O Ω).symm.toRingEquiv.toRingHom
  have he : spMap e ≫ spMap (algebraMap O Ω) = jK O :=
    sp_comp (RingHom.ext fun x => (FractionRing.algEquiv O Ω).symm.commutes x)
  have w : pullback.fst B.A.hom (jK O) ≫ B.A.hom = (pullback.snd B.A.hom (jK O) ≫ spMap e) ≫ spMap (algebraMap O Ω) := by
    rw [Category.assoc, he, pullback.condition]
  have k := hj.1.lift_fst _ _ w
  refine (cls_eq_iff (pull_isLB B.isLB _) (pull_isLB (pull_isLB B'.isLB _) _)).1 ?_
  rw [cls_pull B.isLB, cls_pull (pull_isLB B'.isLB _), cls_pull B'.isLB, ← k, pull_comp, pull_comp,
    ← pull_comp j, hE, ← (iso_iff Q.isLB B.isLB _).1 l, ← (iso_iff Q.isLB B'.isLB _).1 l']

theorem exists_common_fibre {O Ω R' R'' K : Type} [CommRing O] [IsDomain O] [IsLocalRing O] [IsNoetherianRing O]
    [IsIntegrallyClosed O] [Field Ω] [Algebra O Ω] [IsFractionRing O Ω] [CommRing R'] [CommRing R''] [CommRing K]
    (f' : R' →+* O) (f'' : R'' →+* O) (v : O →+* K) (P' : PolAV (Sp R')) (P'' : PolAV (Sp R'')) (Q : PolAV (Sp Ω))
    {b' : Q.A.left ⟶ P'.A.left} {b'' : Q.A.left ⟶ P''.A.left}
    (hb' : IsGrpPullback Q.A P'.A (spMap ((algebraMap O Ω).comp f')) b')
    (hb'' : IsGrpPullback Q.A P''.A (spMap ((algebraMap O Ω).comp f'')) b'')
    (l' : LBIso Q.L (P'.L.pull b')) (l'' : LBIso Q.L (P''.L.pull b'')) :
    ∃ (P₀ : PolAV (Sp K)) (d' : P₀.A.left ⟶ P'.A.left) (d'' : P₀.A.left ⟶ P''.A.left),
      IsGrpPullback P₀.A P'.A (spMap (v.comp f')) d' ∧ IsGrpPullback P₀.A P''.A (spMap (v.comp f'')) d'' ∧
      LBIso P₀.L (P'.L.pull d') ∧ LBIso P₀.L (P''.L.pull d'') ∧
      (∀ (t' : Sp R' ⟶ P'.A.left) (t'' : Sp R'' ⟶ P''.A.left) (w : Sp Ω ⟶ Q.A.left), t' ≫ P'.A.hom = 𝟙 _ →
        t'' ≫ P''.A.hom = 𝟙 _ → w ≫ Q.A.hom = 𝟙 _ → w ≫ b' = spMap ((algebraMap O Ω).comp f') ≫ t' →
        w ≫ b'' = spMap ((algebraMap O Ω).comp f'') ≫ t'' →
        ∃ w₀ : Sp K ⟶ P₀.A.left, w₀ ≫ P₀.A.hom = 𝟙 _ ∧ w₀ ≫ d' = spMap (v.comp f') ≫ t' ∧
          w₀ ≫ d'' = spMap (v.comp f'') ≫ t'') ∧
      ∀ (ε' : P'.A ⟶ P'.A) (ε'' : P''.A ⟶ P''.A) (ε : Q.A ⟶ Q.A), ε.left ≫ b' = b' ≫ ε'.left →
        ε.left ≫ b'' = b'' ≫ ε''.left → ∀ w w₂ : Sp K ⟶ P₀.A.left, w ≫ P₀.A.hom = 𝟙 _ → w₂ ≫ P₀.A.hom = 𝟙 _ →
        w₂ ≫ d'' = w ≫ d'' ≫ ε''.left → w₂ ≫ d' = w ≫ d' ≫ ε'.left := by
  obtain ⟨B, c', -, hc', lc'⟩ := GlobalTheory.PureType.exists_baseChange GlobalTheory.polBaseChange_holds (spMap f') P'
  obtain ⟨B₂, c₂, -, hc₂, lc₂⟩ := GlobalTheory.PureType.exists_baseChange GlobalTheory.polBaseChange_holds (spMap f'') P''
  obtain ⟨j, hj, lj, ej⟩ := exists_factor P' B Q (sp_comp rfl) hc' hb' lc' l'
  obtain ⟨j₂, hj₂, lj₂, ej₂⟩ := exists_factor P'' B₂ Q (sp_comp rfl) hc₂ hb'' lc₂ l''
  obtain ⟨E, hE, lE, eE⟩ := exists_iso B B₂ Q hj hj₂ lj lj₂
  have hc'' : IsGrpPullback B.A P''.A (spMap f'') (E ≫ c₂) := (hE.comp hc₂).congr (Category.id_comp _) rfl
  have lc'' := lb_comp B.isLB B₂.isLB P''.isLB lE lc₂
  have ej'' : j ≫ E ≫ c₂ = b'' := by rw [← Category.assoc, eE, ej₂]
  generalize E ≫ c₂ = c'' at hc'' lc'' ej''
  obtain ⟨P₀, d, -, hd, ld⟩ := GlobalTheory.PureType.exists_baseChange GlobalTheory.polBaseChange_holds (spMap v) B
  obtain ⟨_, _⟩ : QuasiCompact (spMap (algebraMap O Ω)) ∧ IsSchemeTheoreticallyDominant (spMap (algebraMap O Ω)) :=
    ExtUnique.spec_fractionRing O Ω
  have := P''.isAb.proper
  have := B.isAb.smooth
  have : IsSchemeTheoreticallyDominant j := .of_isPullback hj.1.flip
  refine ⟨P₀, d ≫ c', d ≫ c'', (hd.comp hc').congr (sp_comp rfl) rfl, (hd.comp hc'').congr (sp_comp rfl) rfl,
    lb_comp P₀.isLB B.isLB P'.isLB ld lc', lb_comp P₀.isLB B.isLB P''.isLB ld lc'', ?_, ?_⟩
  · intro t' t'' w ht' ht'' hw e' e''
    have w₁ : (spMap f' ≫ t') ≫ P'.A.hom = 𝟙 _ ≫ spMap f' := by rw [Category.assoc, ht']; simp
    have k₁ := hc'.1.lift_fst _ _ w₁
    have k₂ := hc'.1.lift_snd _ _ w₁
    generalize hc'.1.lift _ _ w₁ = t at k₁ k₂
    have a₁ : spMap (algebraMap O Ω) ≫ t = w ≫ j := hc'.1.hom_ext
      (by rw [Category.assoc, k₁, Category.assoc, ej, e', ← Category.assoc, sp_comp rfl])
      (by rw [Category.assoc, k₂, Category.assoc, hj.1.w, reassoc_of% hw, Category.comp_id])
    have a₂ : t ≫ c'' = spMap f'' ≫ t'' := ExtUnique.hom_ext_of_dominant P''.A.hom
      (by rw [Category.assoc, hc''.1.w, reassoc_of% k₂, Category.assoc, ht'', Category.comp_id])
      (spMap (algebraMap O Ω))
      (by rw [reassoc_of% a₁, ej'', e'', ← Category.assoc, sp_comp rfl])
    have w₂ : (spMap v ≫ t) ≫ B.A.hom = 𝟙 _ ≫ spMap v := by rw [Category.assoc, k₂]; simp
    refine ⟨hd.1.lift _ _ w₂, hd.1.lift_snd _ _ w₂, ?_, ?_⟩
    · rw [← Category.assoc, hd.1.lift_fst, Category.assoc, k₁, ← Category.assoc, sp_comp rfl]
    · rw [← Category.assoc, hd.1.lift_fst, Category.assoc, a₂, ← Category.assoc, sp_comp rfl]
  · intro ε' ε'' ε e' e'' w w₂ hw hw₂ h
    have w₁ : (c' ≫ ε'.left) ≫ P'.A.hom = B.A.hom ≫ spMap f' := by rw [Category.assoc, Over.w, hc'.1.w]
    have k₁ := hc'.1.lift_fst _ _ w₁
    have k₂ := hc'.1.lift_snd _ _ w₁
    generalize hc'.1.lift _ _ w₁ = t at k₁ k₂
    have a₁ : j ≫ t = ε.left ≫ j := hc'.1.hom_ext
      (by rw [Category.assoc, k₁, Category.assoc, ej, e', reassoc_of% ej])
      (by rw [Category.assoc, k₂, Category.assoc, hj.1.w, Over.w_assoc])
    have a₂ : t ≫ c'' = c'' ≫ ε''.left := ExtUnique.hom_ext_of_dominant P''.A.hom
      (by rw [Category.assoc, hc''.1.w, reassoc_of% k₂, Category.assoc, Over.w, hc''.1.w]) j
      (by rw [reassoc_of% a₁, ej'', e'', reassoc_of% ej''])
    have a₃ : w₂ ≫ d = w ≫ d ≫ t := hc''.1.hom_ext
      (by simpa only [Category.assoc, a₂] using h)
      (by simp only [Category.assoc, k₂, hd.1.w, reassoc_of% hw, reassoc_of% hw₂])
    rw [reassoc_of% a₃, k₁]
    simp only [Category.assoc]

theorem mono_val {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω)
    (frac : ∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, x = a / b) : Mono (spMap R.val.toRingHom) := by
  have : IsFractionRing R Ω := IsFractionRing.of_field _ _ fun x => by
    obtain ⟨a, ha, b, hb, h⟩ := frac x
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, h⟩
  have : IsPreimmersion (spMap (algebraMap R Ω)) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  exact inferInstanceAs (Mono (spMap (algebraMap R Ω)))

section Model

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω} {φ : Ω →+* Ω} {s : M.Z ⟶ M.Z}

theorem valF_app (hs : M.pt ≫ s = spMap φ ≫ M.pt) {U : M.Z.Opens} (hU : (U : Set M.Z).Nonempty) (a : Γ(M.Z, U)) :
    valF M.pt (s ⁻¹ᵁ U) (s.app U a) = φ (valF M.pt U a) := by
  refine (GlobalTheory.Points.valR_comp M.pt s U a).symm.trans ?_
  rw [hs]
  exact GlobalTheory.Points.valR_spMap_comp _ M.pt U (M.top_le_preimage_pt hU) a

theorem map_mem_O (hs : M.pt ≫ s = spMap φ ≫ M.pt) {z : M.Z} {x : Ω} (hx : x ∈ M.O (s z)) : φ x ∈ M.O z := by
  obtain ⟨U, a, hz, rfl⟩ := hx
  exact ⟨s ⁻¹ᵁ U, s.app U a, hz, valF_app hs ⟨_, hz⟩ a⟩

theorem val_comp (hs : M.pt ≫ s = spMap φ ≫ M.pt) {K : Type} [Field K] (y : Sp K ⟶ M.Z) (w : Sp K) {x : Ω}
    (hx : x ∈ M.O (s (y w))) : M.val (y ≫ s) x = M.val y (φ x) := by
  obtain ⟨U, a, hz, rfl⟩ := hx
  have h1 : Set.range y ⊆ (s ⁻¹ᵁ U : M.Z.Opens) := by
    rw [RatModel.range_eq_singleton y w, Set.singleton_subset_iff]
    exact hz
  rw [RatModel.val_eq h1 (valF_app hs ⟨_, hz⟩ a),
    RatModel.val_valF (U := U) (by rintro _ ⟨w', rfl⟩; exact h1 ⟨w', rfl⟩)]
  exact GlobalTheory.Points.valR_comp y s U a

end Model

theorem exists_generic {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S S' S'' : ThetaSys o Ω} (ρ : S.Real)
    (ε : Matrix (Fin 8) (Fin 8) ℤ → (ρ.P.A ⟶ ρ.P.A)) (ρ' : S'.Real) (ε' : Matrix (Fin 8) (Fin 8) ℤ → (ρ'.P.A ⟶ ρ'.P.A))
    (ρ'' : S''.Real) (ε'' : Matrix (Fin 8) (Fin 8) ℤ → (ρ''.P.A ⟶ ρ''.P.A)) (l' : S.Gam → S'.Gam) (l'' : S.Gam → S''.Gam)
    (h' : Same ρ ε ρ' ε' l' (RingHom.id _)) (h'' : Same ρ ε ρ'' ε'' l'' (RingHom.id _)) (σ : Ω →+* Ω) (a : S.Gam → S.Gam)
    (P₀ : PolAV (Sp Ω)) (b : P₀.A.left ⟶ ρ.P.A.left) (t : P₀.A.left ⟶ P₀.A.left)
    (ε₀ : Matrix (Fin 8) (Fin 8) ℤ → (P₀.A ⟶ P₀.A)) (hb : IsGrpPullback P₀.A ρ.P.A (spMap S.R.val.toRingHom) b)
    (ht : IsGrpPullback P₀.A P₀.A (spMap σ) t) (lb : LBIso P₀.L (ρ.P.L.pull b)) (lt : LBIso P₀.L (P₀.L.pull t))
    (hε : ∀ E, (ε₀ E).left ≫ b = b ≫ (ε E).left ∧ (ε₀ E).left ≫ t = t ≫ (ε₀ E).left)
    (hp : ∀ x (w w' : Sp Ω ⟶ P₀.A.left), w ≫ b = spMap S.R.val.toRingHom ≫ (ρ.pt x).left →
      w' ≫ t = spMap σ ≫ w → w' ≫ b = spMap S.R.val.toRingHom ≫ (ρ.pt (a x)).left) :
    ∃ (Q : PolAV (Sp Ω)) (b' : Q.A.left ⟶ ρ'.P.A.left) (b'' : Q.A.left ⟶ ρ''.P.A.left),
      IsGrpPullback Q.A ρ'.P.A (spMap S'.R.val.toRingHom) b' ∧
      IsGrpPullback Q.A ρ''.P.A (spMap (σ.comp S''.R.val.toRingHom)) b'' ∧
      LBIso Q.L (ρ'.P.L.pull b') ∧ LBIso Q.L (ρ''.P.L.pull b'') ∧
      (∀ x, ∃ w : Sp Ω ⟶ Q.A.left, w ≫ Q.A.hom = 𝟙 _ ∧ w ≫ b' = spMap S'.R.val.toRingHom ≫ (ρ'.pt (l' (a x))).left ∧
        w ≫ b'' = spMap (σ.comp S''.R.val.toRingHom) ≫ (ρ''.pt (l'' x)).left) ∧
      ∀ E, ∃ η : Q.A ⟶ Q.A, η.left ≫ b' = b' ≫ (ε' E).left ∧ η.left ≫ b'' = b'' ≫ (ε'' E).left := by
  obtain ⟨P₁, a₁, a₁', ε₁, ha₁, ha₁', la₁, la₁', he₁, hp₁⟩ := h'
  obtain ⟨P₂, a₂, a₂', ε₂, ha₂, ha₂', la₂, la₂', he₂, hp₂⟩ := h''
  rw [RingHom.id_comp] at ha₁ ha₂ hp₁ hp₂
  have := mono_val S.R S.frac
  have : Mono b := (MorphismProperty.monomorphisms Scheme).of_isPullback hb.1.flip (.infer_property _)
  have : Mono a₂ := (MorphismProperty.monomorphisms Scheme).of_isPullback ha₂.1.flip (.infer_property _)
  obtain ⟨κ₁, hκ₁, lκ₁, eκ₁⟩ := exists_factor ρ.P P₀ P₁ (Category.id_comp _) hb ha₁ lb la₁
  obtain ⟨κ₂, hκ₂, lκ₂, eκ₂⟩ := exists_factor ρ.P P₂ P₀ (Category.id_comp _) ha₂ hb la₂ lb
  have hs : ∀ x, (ρ.pt x).left ≫ ρ.P.A.hom = 𝟙 _ := fun x => Over.w (ρ.pt x)
  refine ⟨P₁, a₁', κ₁ ≫ t ≫ κ₂ ≫ a₂', ha₁', (hκ₁.comp (ht.comp (hκ₂.comp ha₂'))).congr ?_ rfl, la₁',
    lb_comp P₁.isLB P₀.isLB ρ''.P.isLB lκ₁ (lb_comp P₀.isLB P₀.isLB ρ''.P.isLB lt
      (lb_comp P₀.isLB P₂.isLB ρ''.P.isLB lκ₂ la₂')), fun x => ?_, fun E => ⟨ε₁ E, (he₁ E).2, ?_⟩⟩
  · rw [Category.id_comp, Category.id_comp, sp_comp rfl]
  · obtain ⟨w₁, e₁, e₁'⟩ := hp₁ (a x)
    obtain ⟨w₂, e₂, e₂'⟩ := hp₂ x
    have c₁ : (spMap S.R.val.toRingHom ≫ (ρ.pt x).left) ≫ ρ.P.A.hom = 𝟙 _ ≫ spMap S.R.val.toRingHom := by
      rw [Category.assoc, hs]; simp
    have k₁ := hb.1.lift_fst _ _ c₁
    have k₂ := hb.1.lift_snd _ _ c₁
    generalize hb.1.lift _ _ c₁ = w at k₁ k₂
    have c₂ : (spMap σ ≫ w) ≫ P₀.A.hom = 𝟙 _ ≫ spMap σ := by rw [Category.assoc, k₂]; simp
    have k₃ := ht.1.lift_fst _ _ c₂
    generalize ht.1.lift _ _ c₂ = w' at k₃
    have k₄ : w₁ ≫ κ₁ = w' := by
      rw [← cancel_mono b, Category.assoc, eκ₁, e₁, hp x w w' k₁ k₃]
    have k₅ : w ≫ κ₂ = w₂ := by
      rw [← cancel_mono a₂, Category.assoc, eκ₂, k₁, e₂]
    refine ⟨w₁, ?_, e₁', ?_⟩
    · rw [← cancel_mono (spMap S.R.val.toRingHom), Category.assoc, ← ha₁.1.w, reassoc_of% e₁, hs]
      simp
    · rw [reassoc_of% k₄, reassoc_of% k₃, reassoc_of% k₅, e₂', ← Category.assoc, sp_comp rfl]
  · have k₁ : (ε₁ E).left ≫ κ₁ = κ₁ ≫ (ε₀ E).left := by
      rw [← cancel_mono b, Category.assoc, Category.assoc, eκ₁, (he₁ E).1, (hε E).1, reassoc_of% eκ₁]
    have k₂ : (ε₀ E).left ≫ κ₂ = κ₂ ≫ (ε₂ E).left := by
      rw [← cancel_mono a₂, Category.assoc, Category.assoc, eκ₂, (he₂ E).1, (hε E).1, reassoc_of% eκ₂]
    rw [reassoc_of% k₁, reassoc_of% (hε E).2, reassoc_of% k₂, (he₂ E).2]
    simp only [Category.assoc]

theorem exists_to_test {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {p : ℕ}
    [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀) (P₀ : PolAV (Sp (PadicAlgCl p)))
    {d : P₀.A.left ⟶ ρ.P.A.left} (hd : IsGrpPullback P₀.A ρ.P.A (spMap y₀) d) (ld : LBIso P₀.L (ρ.P.L.pull d)) :
    ∃ a : P₀.A.left ⟶ u.A.A.left, IsGrpPullback P₀.A u.A.A (spMap (algebraMap (FractionRing u.V) (PadicAlgCl p))) a ∧
      LBIso P₀.L (u.A.L.pull a) ∧ a ≫ u.φ = d ∧ ∀ w : Sp (PadicAlgCl p) ⟶ P₀.A.left, w ≫ P₀.A.hom = 𝟙 _ →
        ∃ x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A, w ≫ a = x.left := by
  obtain ⟨a, ha, la, ea⟩ := exists_factor ρ.P u.A P₀ (sp_comp u.fac) u.cart hd u.lb ld
  refine ⟨a, ha, la, ea, fun w hw => ⟨Over.homMk (w ≫ a) ?_, rfl⟩⟩
  rw [Category.assoc, ha.1.w, reassoc_of% hw]
  rfl

theorem spread {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [IsNoetherianRing o] (M : RatModel o Ω)
    (hM : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z) {S' S'' : ThetaSys o Ω} (ρ' : S'.Real) (ρ'' : S''.Real)
    (σ : Ω →+* Ω) (s : M.Z ⟶ M.Z) (hs : M.pt ≫ s = spMap σ ≫ M.pt) {p : ℕ} [Fact p.Prime]
    (y : Sp (PadicAlgCl p) ⟶ M.Z) (h' : S'.R ≤ M.O (y (closedPoint (PadicAlgCl p))))
    (h'' : S''.R ≤ M.O ((y ≫ s) (closedPoint (PadicAlgCl p)))) (y₀ : S'.R →+* PadicAlgCl p)
    (y₁ : S''.R →+* PadicAlgCl p) (hy₀ : ∀ a : S'.R, y₀ a = M.val y a) (hy₁ : ∀ a : S''.R, y₁ a = M.val (y ≫ s) a)
    (u : ρ'.UTest p y₀) (u' : ρ''.UTest p y₁) (Q : PolAV (Sp Ω)) {b' : Q.A.left ⟶ ρ'.P.A.left}
    {b'' : Q.A.left ⟶ ρ''.P.A.left} (hb' : IsGrpPullback Q.A ρ'.P.A (spMap S'.R.val.toRingHom) b')
    (hb'' : IsGrpPullback Q.A ρ''.P.A (spMap (σ.comp S''.R.val.toRingHom)) b'')
    (l' : LBIso Q.L (ρ'.P.L.pull b')) (l'' : LBIso Q.L (ρ''.P.L.pull b'')) :
    ∃ (P₀ : PolAV (Sp (PadicAlgCl p))) (a : P₀.A.left ⟶ u.A.A.left) (a' : P₀.A.left ⟶ u'.A.A.left),
      IsGrpPullback P₀.A u.A.A (spMap (algebraMap (FractionRing u.V) (PadicAlgCl p))) a ∧
      IsGrpPullback P₀.A u'.A.A (spMap (algebraMap (FractionRing u'.V) (PadicAlgCl p))) a' ∧
      LBIso P₀.L (u.A.L.pull a) ∧ LBIso P₀.L (u'.A.L.pull a') ∧
      (∀ (k' : S'.Gam) (k'' : S''.Gam) (w : Sp Ω ⟶ Q.A.left), w ≫ Q.A.hom = 𝟙 _ →
        w ≫ b' = spMap S'.R.val.toRingHom ≫ (ρ'.pt k').left →
        w ≫ b'' = spMap (σ.comp S''.R.val.toRingHom) ≫ (ρ''.pt k'').left →
        ∃ (w : Sp (PadicAlgCl p) ⟶ P₀.A.left) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)
          (x' : TFK (R := u'.V) (PadicAlgCl p) ⟶ u'.A.A), w ≫ P₀.A.hom = 𝟙 _ ∧ w ≫ a = x.left ∧ w ≫ a' = x'.left ∧
          x.left ≫ u.φ = spMap y₀ ≫ (ρ'.pt k').left ∧ x'.left ≫ u'.φ = spMap y₁ ≫ (ρ''.pt k'').left) ∧
      ∀ (ε' : ρ'.P.A ⟶ ρ'.P.A) (ε'' : ρ''.P.A ⟶ ρ''.P.A) (ε : Q.A ⟶ Q.A), ε.left ≫ b' = b' ≫ ε'.left →
        ε.left ≫ b'' = b'' ≫ ε''.left → ∀ w w₂ : Sp (PadicAlgCl p) ⟶ P₀.A.left, w ≫ P₀.A.hom = 𝟙 _ →
        w₂ ≫ P₀.A.hom = 𝟙 _ → w₂ ≫ a' ≫ u'.φ = w ≫ a' ≫ u'.φ ≫ ε''.left → w₂ ≫ a ≫ u.φ = w ≫ a ≫ u.φ ≫ ε'.left := by
  let z := y (closedPoint (PadicAlgCl p))
  have := M.isNoetherianRing_O z
  have := RatModel.isIntegrallyClosed_O hM z
  let f' : S'.R →+* M.O z := (Subalgebra.inclusion h').toRingHom
  let f'' : S''.R →+* M.O z := (σ.comp S''.R.val.toRingHom).codRestrict (M.O z) fun x => map_mem_O hs (h'' x.2)
  let v : M.O z →+* PadicAlgCl p := RatModel.valHom y z (RatModel.range_eq_singleton y _)
  have e₀ : v.comp f' = y₀ := RingHom.ext fun x => (hy₀ x).symm
  have e₁ : v.comp f'' = y₁ := RingHom.ext fun x => ((hy₁ x).trans (val_comp hs y _ (h'' x.2))).symm
  obtain ⟨P₀, d', d'', hd', hd'', ld', ld'', hp, hε⟩ := exists_common_fibre f' f'' v ρ'.P ρ''.P Q (b' := b') (b'' := b'')
    hb' hb'' l' l''
  rw [e₀] at hd' hp
  rw [e₁] at hd'' hp
  obtain ⟨a, ha, la, ea, xa⟩ := exists_to_test u P₀ hd' ld'
  obtain ⟨a', ha', la', ea', xa'⟩ := exists_to_test u' P₀ hd'' ld''
  refine ⟨P₀, a, a', ha, ha', la, la', fun k' k'' w hw c' c'' => ?_, fun ε' ε'' ε c' c'' w w₂ hw hw₂ h => ?_⟩
  · obtain ⟨w₀, hw₀, g', g''⟩ := hp (ρ'.pt k').left (ρ''.pt k'').left w (Over.w (ρ'.pt k')) (Over.w (ρ''.pt k'')) hw c' c''
    obtain ⟨x, hx⟩ := xa w₀ hw₀
    obtain ⟨x', hx'⟩ := xa' w₀ hw₀
    refine ⟨w₀, x, x', hw₀, hx, hx', ?_, ?_⟩
    · rw [← hx, Category.assoc, ea, g']
    · rw [← hx', Category.assoc, ea', g'']
  · rw [ea, reassoc_of% ea]
    rw [ea', reassoc_of% ea'] at h
    exact hε ε' ε'' ε c' c'' w w₂ hw hw₂ h

end GlobalTheory.Poinc.GalTrans
