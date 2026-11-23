import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Statements.HeckeInFamilies.GenericMemChart
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.OpenImmersionCompStructureEqGeneric
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MapToUniversalObjectUnique
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSimilitudeOfAutModLevelIdeal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsObjTwistBySimilitude
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.LevActs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem spMap_id' (R : Type) [CommRing R] : spMap (RingHom.id R) = 𝟙 (Sp R) := Spec.map_id _

theorem exists_sab_inv {S : Scheme.{0}} {t : SAB H S} (e : S ≅ S) (n : SABMap t t e.hom) :
    ∃ n' : SABMap t t e.inv, n'.φ ≫ n.φ = 𝟙 _ ∧ n.φ ≫ n'.φ = 𝟙 _ := by
  obtain ⟨i, hi⟩ := ObjMaps.exists_sab_id t
  obtain ⟨i', hi'⟩ := LevUniq.exists_sab_cast i e.inv_hom_id.symm
  obtain ⟨n', hn'⟩ := ObjMaps.exists_sab_cancel n i'
  have h : n'.φ ≫ n.φ = 𝟙 _ := hn'.symm.trans (hi'.trans hi)
  have pn : IsPullback n.φ t.G.hom t.G.hom e.hom := n.cart.1
  have : IsIso n.φ := pn.isIso_fst_of_isIso
  refine ⟨n', h, ?_⟩
  rw [← cancel_mono n.φ, Category.assoc, h, Category.comp_id, Category.id_comp]

section

variable {U U' : Scheme.{0}} {F F' : Type} [Field F] [Field F'] {c : U ⟶ Sp F} {c' : U' ⟶ Sp F'} {t₀ : SAB H U}
  {t₀' : SAB H U'} {O O' : Type} [CommRing O] [CommRing O'] {β : O →+* F} {β' : O' →+* F'}

theorem exists_lift_end {C' : Cpt c' t₀' β'} {C : Cpt c t₀ β} {b : O →+* O'} {r : U' ⟶ U} {ν : SABMap t₀' t₀ r}
    (a : C'.Above C b r ν) (hD : IsDedFrac β') (e' : U' ⟶ U') (n' : SABMap t₀' t₀' e') (ρ : C.X ⟶ C.X)
    (mu : SABMap C.t C.t ρ) (he' : e' ≫ c' = c') (hρ : ρ ≫ C.s = C.s) (hj : r ≫ C.j ≫ ρ = e' ≫ r ≫ C.j)
    (hφ : ν.φ ≫ C.m.φ ≫ mu.φ = n'.φ ≫ ν.φ ≫ C.m.φ) :
    ∃ (h : C'.X ⟶ C'.X) (mu' : SABMap C'.t C'.t h), h ≫ C'.s = C'.s ∧ C'.j ≫ h = e' ≫ C'.j ∧
      C'.m.φ ≫ mu'.φ = n'.φ ≫ C'.m.φ := by
  obtain ⟨m, hm⟩ := ObjMaps.exists_sab_comp mu a.mu
  obtain ⟨h, mu', hh, -, -, h₁, h₂, -⟩ := Cpt.Above.exists_lift E H U F O c t₀ β U' F' O' c' t₀' β' U' F' O' c' t₀' β'
    C C' C' b (RingHom.id _) (RingHom.id _) r ν a e' n' (a.π ≫ ρ) m
    (by rw [Category.assoc, hρ, a.π_over, RingHom.id_comp]) hD (by rw [RingHom.id_comp, RingHom.comp_id])
    (by rw [he', spMap_id', Category.comp_id]) (by rw [← Category.assoc, a.j_comm, Category.assoc, hj])
    (by rw [hm, ← Category.assoc, a.φ_comm, Category.assoc, hφ])
  exact ⟨h, mu', by rw [hh, spMap_id', Category.comp_id], h₁, h₂⟩

theorem hom_ext_j (C : Cpt c t₀ β) (hD : IsDedFrac β) {f g : C.X ⟶ C.X} (h : C.j ≫ f = C.j ≫ g) : f = g := by
  obtain ⟨⟨_, _⟩, -, hfr⟩ := hD
  letI := β.toAlgebra
  obtain ⟨-, -, hS, -, -, h3, -⟩ :=
    GlobalTheory.genericPart_dense_proOpen O F C.X U C.s C.jQ C.flat C.proj C.jQ_open C.jQ_dense
  have : ∀ x : C.X, _root_.IsReduced (C.X.presheaf.stalk x) := fun x ↦
    have := (C.normal x).1
    inferInstance
  have := isReduced_of_isReduced_stalk C.X
  have : IsDominant C.j := h3
  exact ext_of_isDominant C.j h

theorem extendsAut_up {C' : Cpt c' t₀' β'} {C : Cpt c t₀ β} {b : O →+* O'} {r : U' ⟶ U} {ν : SABMap t₀' t₀ r}
    (a : C'.Above C b r ν) (hD : IsDedFrac β') (e' : U' ≅ U') (n' : SABMap t₀' t₀' e'.hom) (e : U ≅ U)
    (n : SABMap t₀ t₀ e.hom) (he' : e'.hom ≫ c' = c') (hr : e'.hom ≫ r = r ≫ e.hom)
    (hν : n'.φ ≫ ν.φ = ν.φ ≫ n.φ) (hC : C.ExtendsAut e n) : C'.ExtendsAut e' n' := by
  obtain ⟨ρ, mu, h₁, h₂, h₃⟩ := hC
  obtain ⟨ni, hni, -⟩ := exists_sab_inv e' n'
  obtain ⟨mi, -, hmi⟩ := exists_sab_inv ρ mu
  have hj : r ≫ C.j ≫ ρ.hom = e'.hom ≫ r ≫ C.j := by rw [h₂, ← Category.assoc, ← hr, Category.assoc]
  have hφ : ν.φ ≫ C.m.φ ≫ mu.φ = n'.φ ≫ ν.φ ≫ C.m.φ := by rw [h₃, ← Category.assoc, ← hν, Category.assoc]
  obtain ⟨h, mu', k₁, k₂, k₃⟩ := exists_lift_end a hD e'.hom n' ρ.hom mu he' h₁ hj hφ
  obtain ⟨h', -, -, k₂', -⟩ := exists_lift_end a hD e'.inv ni ρ.inv mi (by rw [Iso.inv_comp_eq, he'])
    (by rw [Iso.inv_comp_eq, h₁])
    (by
      rw [Iso.eq_inv_comp, ← cancel_mono ρ.hom]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      exact hj.symm)
    (by
      calc ν.φ ≫ C.m.φ ≫ mi.φ = (ni.φ ≫ n'.φ) ≫ ν.φ ≫ C.m.φ ≫ mi.φ := by rw [hni, Category.id_comp]
        _ = ni.φ ≫ (n'.φ ≫ ν.φ ≫ C.m.φ) ≫ mi.φ := by simp only [Category.assoc]
        _ = ni.φ ≫ ν.φ ≫ C.m.φ ≫ mu.φ ≫ mi.φ := by rw [← hφ]; simp only [Category.assoc]
        _ = ni.φ ≫ ν.φ ≫ C.m.φ := by rw [hmi, Category.comp_id])
  refine ⟨⟨h, h', hom_ext_j C' hD ?_, hom_ext_j C' hD ?_⟩, mu', k₁, k₂, k₃⟩
  · rw [← Category.assoc, k₂, Category.assoc, k₂', Iso.hom_inv_id_assoc, Category.comp_id]
  · rw [← Category.assoc, k₂', Category.assoc, k₂, Iso.inv_hom_id_assoc, Category.comp_id]

theorem extendsAut_of_isEmpty [IsEmpty U] (C : Cpt c t₀ β) (e : U ≅ U) (n : SABMap t₀ t₀ e.hom) :
    C.ExtendsAut e n := by
  obtain ⟨i, -⟩ := ObjMaps.exists_sab_id C.t
  have : IsEmpty t₀.G.left := Function.isEmpty (t₀.G.hom : t₀.G.left → U)
  exact ⟨Iso.refl _, i, Category.id_comp _, isInitialOfIsEmpty.hom_ext _ _, isInitialOfIsEmpty.hom_ext _ _⟩

end

theorem mono_spMap {l : Level H} (hA : l.A = 1) {S : ℕ} (β : RZ H S 1 →+* KA l)
    (hβ : IsInc (RZ H S 1).subtype (KA l).val.toRingHom β) : Mono (spMap β) := by
  have : Epi (CommRingCat.ofHom β) := by
    refine ⟨fun {R} f g h => ?_⟩
    have h' : ∀ x, f.hom (β x) = g.hom (β x) := fun x => congrArg (fun k => k.hom x) h
    have hw : ∀ (x : ℂ) (hx : x ∈ RZ H S 1) (hx' : x ∈ KA l), f.hom ⟨x, hx'⟩ = g.hom ⟨x, hx'⟩ := fun x hx hx' => by
      have : β ⟨x, hx⟩ = ⟨x, hx'⟩ := Subtype.ext (hβ ⟨x, hx⟩)
      rw [← this, h']
    ext ⟨x, hx⟩
    change (⟨x, hx⟩ : KA l) ∈ RingHom.eqLocusField f.hom g.hom
    induction hx using IntermediateField.adjoin_induction with
    | mem x hx =>
      refine hw x ?_ _
      rcases hx with rfl | rfl
      · have h2 : (1 + H.rt0) / 2 ∈ RZ H S 1 := Subring.subset_closure (Or.inl rfl)
        convert sub_mem (add_mem h2 h2) (one_mem _) using 1
        ring
      · rw [hA]
        exact Subring.subset_closure (Or.inr (Or.inr rfl))
    | algebraMap q => exact SubfieldClass.ratCast_mem (RingHom.eqLocusField f.hom g.hom) q
    | add x y hx hy ihx ihy => exact add_mem ihx ihy
    | inv x hx ih => exact inv_mem ih
    | mul x y hx hy ihx ihy => exact mul_mem ihx ihy
  exact inferInstanceAs (Mono (Scheme.Spec.map (CommRingCat.ofHom β).op))

variable {D : Datum H}

section

variable {l : Level H} {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B}

theorem eta_zero (o : Obj D l b s) : o.eta 0 = 1 := o.eta_ker 0 (Submodule.zero_mem _)

theorem eta_nsmul (o : Obj D l b s) (n : ℕ) (a : D.La) : o.eta (n • a) = o.eta a ^ n := by
  induction n with
  | zero => rw [zero_smul, pow_zero, eta_zero]
  | succ n ih => rw [succ_nsmul, o.eta_add, ih, pow_succ]

theorem eta_congr (o : Obj D l b s) {x y : D.La} (h : x - y ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La)) :
    o.eta x = o.eta y := by
  rw [← sub_add_cancel x y, o.eta_add, o.eta_ker _ h, _root_.one_mul]

theorem etaA_eq (o : Obj D l b s) (hA : l.A = 1) (a : D.La) : o.etaA a = o.eta 0 := by
  rw [eta_zero, ← o.etaA_ker a, hA, one_smul]

theorem mem_of_eta_eq_one [Nonempty S] (o : Obj D l b s) {a : D.La} (ha : o.eta a = 1) :
    a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) := by
  obtain ⟨p⟩ := ‹Nonempty S›
  let k : Type := AlgebraicClosure (S.residueField p)
  let x : Sp k ⟶ S := Spec.map (CommRingCat.ofHom (algebraMap (S.residueField p) k)) ≫ S.fromSpecResidueField p
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (x ≫ s)
  obtain ⟨-, I, -, -, hI⟩ := o.geom k x φ.hom hφ.symm
  obtain ⟨e, he, e', he', hee⟩ := Submodule.mem_sup.mp (l.coprime ▸ Submodule.mem_top : (1 : 𝓞 E) ∈
    l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E))
  have hsub : a - e' • a = e • a := by rw [sub_eq_iff_eq_add, ← add_smul, hee, one_smul]
  have hm : a - e' • a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) := hsub ▸ Submodule.smul_mem_smul he Submodule.mem_top
  have h₁ := hI (e' • a) (Submodule.smul_mem_smul he' Submodule.mem_top)
  rw [← eta_congr o hm, ha, MonObj.comp_one] at h₁
  have hM : 0 < l.M := by have := l.three_le; omega
  have h₂ := SimMb.mem_of_modN D l ((I.ker l.M hM _).1 h₁.symm)
  simpa using add_mem hm h₂

end

theorem map_unique (hL : Out.Laws) {l : Level H} (hA : l.A = 1) (Xo : Moduli D l) {S : Scheme.{0}} (hS : IsReduced S)
    {t : SAB H S} {r r' : S ⟶ Xo.X} (ν : SABMap t Xo.univ.t r) (ν' : SABMap t Xo.univ.t r')
    (hs : r ≫ Xo.s = r' ≫ Xo.s)
    (h : ∀ a, ∃ y : 𝟙_ (Over S) ⟶ t.G, y.left ≫ ν.φ = r ≫ (Xo.univ.eta a).left ∧
      y.left ≫ ν'.φ = r' ≫ (Xo.univ.eta a).left) : r = r' ∧ ν.φ = ν'.φ := by
  obtain ⟨o₁, ⟨m₁⟩⟩ := obj_pull E H D l (KA l) (KA l) (baseKA l) (baseKA l) (RingHom.id _) Xo.X S Xo.s
    (r ≫ Xo.s) r rfl rfl (by rw [spMap_id', Category.comp_id]) Xo.univ
  obtain ⟨n₁, hn₁⟩ := LevUniq.exists_sab_cast m₁.toSABMap (Category.id_comp r).symm
  obtain ⟨k, hk⟩ := ObjMaps.exists_sab_cancel ν n₁
  have hk' : m₁.toSABMap.φ = k.φ ≫ ν.φ := hn₁.symm.trans hk
  have pk : IsPullback k.φ o₁.t.G.hom t.G.hom (𝟙 S) := k.cart.1
  have pν : IsPullback ν.φ t.G.hom Xo.univ.t.G.hom r := ν.cart.1
  have key : ∀ (x : 𝟙_ (Over S) ⟶ o₁.t.G) (y : 𝟙_ (Over S) ⟶ t.G),
      x.left ≫ m₁.toSABMap.φ = y.left ≫ ν.φ → x.left ≫ k.φ = y.left := by
    intro x y h
    refine pν.hom_ext ?_ ?_
    · rw [Category.assoc, ← hk', h]
    · rw [Category.assoc, pk.w, Category.comp_id, Over.w x, Over.w y]
  obtain ⟨n₂, hn₂⟩ := ObjMaps.exists_sab_comp ν' k
  obtain ⟨n₃, hn₃⟩ := LevUniq.exists_sab_cast n₂ (Category.id_comp r')
  have h₃ : n₃.φ = k.φ ≫ ν'.φ := hn₃.trans hn₂
  have e₁ : ∀ a, (o₁.eta a).left ≫ n₃.φ = r' ≫ (Xo.univ.eta a).left := by
    intro a
    obtain ⟨y, hy, hy'⟩ := h a
    rw [h₃, ← Category.assoc, key _ _ ((m₁.eta a).trans hy.symm), hy']
  have e₂ : ∀ a, (o₁.etaA a).left ≫ n₃.φ = r' ≫ (Xo.univ.etaA a).left := by
    intro a
    rw [etaA_eq _ hA, etaA_eq _ hA, e₁]
  have hr : r = r' := (Xo.rep S (r ≫ Xo.s) hS o₁).unique ⟨rfl, ⟨m₁⟩⟩ ⟨hs.symm, ⟨⟨n₃, e₁, e₂⟩⟩⟩
  subst hr
  refine ⟨rfl, ?_⟩
  have hφ : m₁.toSABMap.φ = n₃.φ :=
    obj_rigid_closed hL E H D l (KA l) (KA l) (baseKA l) (baseKA l) Xo.X S Xo.s (r ≫ Xo.s) Xo.univ o₁ r
      (Or.inl hS) m₁.toSABMap n₃ (fun a => ⟨_, m₁.eta a, e₁ a⟩)
  have : IsIso k.φ := pk.isIso_fst_of_isIso
  rw [← cancel_epi k.φ, ← hk', ← h₃, hφ]

theorem isReduced_X {l : Level H} (Xo : Moduli D l) : IsReduced Xo.X :=
  have := Xo.smooth
  (isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ Xo.s
    (SmoothOfRelativeDimension.smooth D.dim Xo.s)).1

theorem isReduced_XF {l : Level H} (Xo : Moduli D l) (c : Coeff l) : IsReduced (Xo.XF c) :=
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  (isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ (pullback.snd _ _) inferInstance).1

theorem exists_end (hD : 1 ≤ D.p + D.q) {l : Level H} (hA : l.A = 1) (Xo : Moduli D l) (ω : Sim D) :
    ∃ (f : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t f), f ≫ Xo.s = Xo.s ∧
      ∀ a, (Xo.univ.eta (ω.f l.M a)).left ≫ ν.φ = f ≫ (Xo.univ.eta a).left := by
  obtain ⟨f, hf, ⟨m⟩⟩ := (Xo.rep Xo.X Xo.s (isReduced_X Xo) (LevelTwist.objTwist Xo.univ ω
    ((SimAlg.sim_group E H D hD).1 ω) (by rw [hA]; exact one_dvd _))).exists
  exact ⟨f, m.toSABMap, hf, m.eta⟩

theorem comp_eq_id (hL : Out.Laws) {l : Level H} (hA : l.A = 1) (Xo : Moduli D l) {g g' : D.La → D.La}
    {f f' : Xo.X ⟶ Xo.X} (ν : SABMap Xo.univ.t Xo.univ.t f) (ν' : SABMap Xo.univ.t Xo.univ.t f')
    (hf : f ≫ Xo.s = Xo.s) (hf' : f' ≫ Xo.s = Xo.s)
    (h : ∀ a, (Xo.univ.eta (g a)).left ≫ ν.φ = f ≫ (Xo.univ.eta a).left)
    (h' : ∀ a, (Xo.univ.eta (g' a)).left ≫ ν'.φ = f' ≫ (Xo.univ.eta a).left)
    (hg : ∀ a, D.ModN l.M (g (g' a) - a)) : f ≫ f' = 𝟙 _ := by
  obtain ⟨n, hn⟩ := ObjMaps.exists_sab_comp ν' ν
  obtain ⟨i, hi⟩ := ObjMaps.exists_sab_id Xo.univ.t
  refine (map_unique hL hA Xo (isReduced_X Xo) n i (by rw [Category.assoc, hf', hf, Category.id_comp])
    fun a => ⟨Xo.univ.eta a, ?_, by rw [hi, Category.comp_id, Category.id_comp]⟩).1
  conv_lhs => rw [← eta_congr _ (SimMb.mem_of_modN D l (hg a))]
  rw [hn, ← Category.assoc, h, Category.assoc, h', Category.assoc]

theorem exists_aut (hL : Out.Laws) (hD : 1 ≤ D.p + D.q) {l : Level H} (hA : l.A = 1) (Xo : Moduli D l)
    (g : D.La →ₗ[𝓞 E] D.La)
    (hg : ∀ x, g x ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) → x ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La)) :
    ∃ (e : Xo.X ≅ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t e.hom), e.hom ≫ Xo.s = Xo.s ∧
      ∀ a, (Xo.univ.eta (g a)).left ≫ ν.φ = e.hom ≫ (Xo.univ.eta a).left := by
  have hM : 0 < l.M := by have := l.three_le; omega
  obtain ⟨ω, hω, -⟩ := exists_sim_of_aut_mod E H D l 1 g hD one_pos (Nat.coprime_one_left _) hg
  obtain ⟨ω', hω'⟩ := (SimAlg.sim_group E H D hD).2.2.2 ω
  obtain ⟨f, ν, hf, h⟩ := exists_end hD hA Xo ω
  obtain ⟨f', ν', hf', h'⟩ := exists_end hD hA Xo ω'
  refine ⟨⟨f, f', comp_eq_id hL hA Xo ν ν' hf hf' h h' fun a => ((hω' _ hM).1 a).2,
    comp_eq_id hL hA Xo ν' ν hf' hf h' h fun a => ((hω' _ hM).1 a).1⟩, ν, hf, fun a => ?_⟩
  rw [← eta_congr _ (hω a)]
  exact h a

theorem levelActs_of_raises : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N : ℕ) (T : Top Xo n N), 1 ≤ D.p + D.q → ∀ (l₀ : Level H) (B : BaseModel T l₀) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model (Xo l) c β), l₀.Dvd l → IsDedFrac β → Raises B Y → Y.LevelActs := by
  intro hL _ _ E _ _ _ H D Xo n N T hD l₀ B l c O _ β Y hl hβ hR r ν gM gA hr hM _
  obtain ⟨b, r', ν', -, hlev, ⟨a⟩⟩ := hR
  change (ofModel Y).ExtendsAut r ν
  rcases isEmpty_or_nonempty ((Xo l).XF c) with _ | _
  · exact extendsAut_of_isEmpty _ r ν
  have hinj : ∀ x, gM x ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) → x ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) := by
    intro x hx
    refine mem_of_eta_eq_one Y.oF (Over.OverMorphism.ext ?_)
    rw [← cancel_epi r.hom, ← hM x, ← eta_zero Y.oF, ← hM 0, map_zero, eta_zero, Y.oF.eta_ker _ hx]
  obtain ⟨h, hh⟩ := SimMb.exists_left_inv D l gM hinj
  have hinj₀ : ∀ x, gM x ∈ l₀.Mb • (⊤ : Submodule (𝓞 E) D.La) → x ∈ l₀.Mb • (⊤ : Submodule (𝓞 E) D.La) := by
    intro x hx
    simpa using sub_mem (LevelTwist.map_mem_smul_top h _ hx) (Submodule.smul_mono hl.2.1 le_rfl (hh x))
  obtain ⟨e, ν₀, he, hν₀⟩ := exists_aut hL hD B.A_one (Xo l₀) gM hinj₀
  obtain ⟨n₁, hn₁⟩ := ObjMaps.exists_sab_comp ν' ν
  obtain ⟨n₂, hn₂⟩ := ObjMaps.exists_sab_comp ν₀ ν'
  have hs : (r.hom ≫ r') ≫ (Xo l₀).s = (r' ≫ e.hom) ≫ (Xo l₀).s := by
    have := mono_spMap B.A_one B.β B.β_inc
    have h₁ : (r' ≫ (Xo l₀).s) ≫ spMap B.β = pullback.snd _ _ ≫ spMap β ≫ spMap b := by
      rw [Category.assoc, ← Cpt.openImmersion_comp_structure_eq_generic B.C, ← Category.assoc, ← a.j_comm, Category.assoc, a.π_over,
        ← Category.assoc, Cpt.openImmersion_comp_structure_eq_generic, Category.assoc]
    rw [Category.assoc, Category.assoc, he, ← cancel_mono (spMap B.β), Category.assoc, h₁, ← Category.assoc, hr]
  obtain ⟨k₁, k₂⟩ := map_unique hL B.A_one (Xo l₀) (isReduced_XF _ c) n₁ n₂ hs fun x =>
    ⟨Y.oF.eta (gM x) ^ (l.M / l₀.M), by
      rw [hn₁, ← Category.assoc, ← eta_nsmul, ← map_nsmul, hM, eta_nsmul, Category.assoc, hlev.1, Category.assoc],
      by rw [hn₂, ← Category.assoc, hlev.1, Category.assoc, hν₀, Category.assoc]⟩
  exact extendsAut_up a hβ r ν e ν₀ hr k₁ (hn₁.symm.trans (k₂.trans hn₂)) (B.acts e ν₀ gM he hν₀)

end GlobalTheory.LevActs
