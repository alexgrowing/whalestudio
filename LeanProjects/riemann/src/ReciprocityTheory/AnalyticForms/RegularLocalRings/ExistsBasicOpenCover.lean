import ReciprocityTheory.AnalyticForms.RegularLocalRings.StalkLoc
import ReciprocityTheory.AnalyticForms.RegularLocalRings.IsOpenAlt
import ReciprocityTheory.AnalyticForms.RegularLocalRings.ExistsMulMemOfAlgebraMapLocRingEqZero

namespace ReciprocityTheory.AnForm.R

open AlgebraicGeometry CategoryTheory MvPolynomial TopologicalSpace IrreducibleComponentPreimages

noncomputable section

section Top

variable {α : Type*} [TopologicalSpace α]

def comps (T : Set α) : Set (Set α) :=
  {C | Maximal (fun C => IsIrreducible C ∧ C ⊆ T) C}

private theorem isIrreducible_preimage_coe_of_subset (T D : Set α) (hDT : D ⊆ T) (hD : IsIrreducible D) :
    IsIrreducible ((↑) ⁻¹' D : Set T) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨y, hy⟩ := hD.1
    exact ⟨⟨y, hDT hy⟩, hy⟩
  · intro u v hu hv hau hbv
    obtain ⟨u', hu', rfl⟩ := isOpen_induced_iff.1 hu
    obtain ⟨v', hv', rfl⟩ := isOpen_induced_iff.1 hv
    obtain ⟨a, ha, hau⟩ := hau
    obtain ⟨b, hb, hbv⟩ := hbv
    obtain ⟨c, hc, hcu, hcv⟩ := hD.2 u' v' hu' hv' ⟨a.1, ha, hau⟩ ⟨b.1, hb, hbv⟩
    exact ⟨⟨c, hDT hc⟩, hc, hcu, hcv⟩

theorem comps_finite [NoetherianSpace α] (T : Set α) : (comps T).Finite := by
  have hfin : (irreducibleComponents T).Finite := NoetherianSpace.finite_irreducibleComponents
  refine (hfin.image (fun S : Set T => ((↑) '' S : Set α))).subset ?_
  intro C hC
  have hC' : Maximal (fun C => IsIrreducible C ∧ C ⊆ T) C := hC
  have himg : ((↑) '' ((↑) ⁻¹' C : Set T) : Set α) = C := by
    rw [Subtype.image_preimage_coe, Set.inter_eq_right.2 hC'.1.2]
  refine ⟨(↑) ⁻¹' C, ⟨isIrreducible_preimage_coe_of_subset T C hC'.1.2 hC'.1.1, fun S hS hCS => ?_⟩, himg⟩
  have hSI : IsIrreducible ((↑) '' S : Set α) := hS.image _ continuous_subtype_val.continuousOn
  have hle := hC'.2 ⟨hSI, by rintro _ ⟨z, -, rfl⟩; exact z.2⟩
    (by rw [← himg]; exact Set.image_mono hCS)
  intro z hz
  exact hle ⟨z, hz, rfl⟩

theorem isClosed_of_mem_comps {T : Set α} (hT : IsClosed T) {C : Set α} (hC : C ∈ comps T) :
    IsClosed C := by
  have hC' : Maximal (fun C => IsIrreducible C ∧ C ⊆ T) C := hC
  have hcl : closure C ≤ C := hC'.2 ⟨hC'.1.1.closure, closure_minimal hC'.1.2 hT⟩ subset_closure
  exact closure_subset_iff_isClosed.1 hcl

theorem sUnion_comps (T : Set α) : ⋃₀ comps T = T := by
  refine Set.Subset.antisymm (Set.sUnion_subset fun C hC => hC.1.2) fun x hx => ?_
  let y : T := ⟨x, hx⟩
  have hI : IsIrreducible (irreducibleComponent y) := isIrreducible_irreducibleComponent
  refine ⟨(↑) '' irreducibleComponent y,
    ⟨⟨hI.image _ continuous_subtype_val.continuousOn, by rintro _ ⟨z, -, rfl⟩; exact z.2⟩, ?_⟩,
    ⟨y, mem_irreducibleComponent, rfl⟩⟩
  intro D hD hCD
  have hpre := isIrreducible_preimage_coe_of_subset T D hD.2 hD.1
  have hsub : irreducibleComponent y ⊆ (↑) ⁻¹' D := fun z hz => hCD ⟨z, hz, rfl⟩
  have hle := (irreducibleComponent_mem_irreducibleComponents y).2 hpre hsub
  intro d hd
  exact ⟨⟨d, hD.2 hd⟩, hle hd, rfl⟩

end Top

variable {W : Scheme.{0}}

def IsBranch (T : Set W) {U : W.Opens} (f : Γ(W, U)) (y : W) (C : Set W) : Prop :=
  C ∈ comps T ∧ y ∈ C ∧ ∃ h : IsIrreducible C, h.genericPoint ∈ U ∧ h.genericPoint ∈ W.zeroLocus {f}

theorem existsUnique_branch [IsNoetherian W] {Z : W.IdealSheafData} (y : W) (U : W.affineOpens)
    (hy : y ∈ U.1) {n : ℕ} (f : Fin n → Γ(W, U.1)) (J : Finset (Fin n))
    [IsRegularLocalRing (W.presheaf.stalk y)]
    (hrsp : FinalTheorems.Rsp (W.presheaf.stalk y) n (fun i => W.presheaf.germ U.1 y hy (f i)))
    (hZU : Z.ideal U = Ideal.span {∏ i ∈ J, f i}) (i : Fin n) (hi : i ∈ J) :
    ∃! C, IsBranch (Z.support : Set W) (f i) y C := by
  exact existsUnique_branchH y U hy f J hrsp hZU i hi

theorem branch_ne [IsNoetherian W] {Z : W.IdealSheafData} (y : W) (U : W.affineOpens)
    (hy : y ∈ U.1) {n : ℕ} (f : Fin n → Γ(W, U.1)) (J : Finset (Fin n))
    [IsRegularLocalRing (W.presheaf.stalk y)]
    (hrsp : FinalTheorems.Rsp (W.presheaf.stalk y) n (fun i => W.presheaf.germ U.1 y hy (f i)))
    (hZU : Z.ideal U = Ideal.span {∏ i ∈ J, f i}) {i j : Fin n} (hi : i ∈ J) (hj : j ∈ J)
    (hij : i ≠ j) {C C' : Set W} (hC : IsBranch (Z.support : Set W) (f i) y C)
    (hC' : IsBranch (Z.support : Set W) (f j) y C') : C ≠ C' := by
  exact branch_neH y U hy f J hrsp hZU hi hj hij hC hC'

theorem exists_open_comps [IsNoetherian W] {Z : W.IdealSheafData} (y : W) (U : W.affineOpens)
    (hy : y ∈ U.1) {n : ℕ} (f : Fin n → Γ(W, U.1)) (J : Finset (Fin n))
    [IsRegularLocalRing (W.presheaf.stalk y)]
    (hrsp : FinalTheorems.Rsp (W.presheaf.stalk y) n (fun i => W.presheaf.germ U.1 y hy (f i)))
    (hZU : Z.ideal U = Ideal.span {∏ i ∈ J, f i}) :
    ∃ O : W.Opens, y ∈ O ∧ O ≤ U.1 ∧ ∀ C ∈ comps (Z.support : Set W),
      C ∩ O = {z ∈ (O : Set W) | ∃ i ∈ J, IsBranch (Z.support : Set W) (f i) y C ∧
        z ∈ W.zeroLocus {f i}} := by
  exact exists_open_compsH y U hy f J hrsp hZU

section Chart

variable {s : W ⟶ Spec (.of ℂ)}

theorem AffPres.isAffineOpen (P : AffPres s) : IsAffineOpen P.V := by
  first
  | exact IsAffine.of_isIso P.iso.hom
  | exact AlgebraicGeometry.isAffine_of_isIso P.iso.hom
  | exact (inferInstance : IsAffine (Spec (.of (MvPolynomial (Fin P.n) ℂ ⧸ P.K)))).of_isIso P.iso.hom
  | exact isAffine_of_isIso P.iso.hom

def AffPres.affOpen (P : AffPres s) : W.affineOpens := ⟨P.V, P.isAffineOpen⟩

def AffPres.bdIdeal (P : AffPres s) (Z : W.IdealSheafData) : Ideal (MvPolynomial (Fin P.n) ℂ) :=
  (Z.ideal P.affOpen).comap P.secHom

theorem AffPres.le_bdIdeal (P : AffPres s) (Z : W.IdealSheafData) : P.K ≤ P.bdIdeal Z := by
  intro g hg
  show P.secHom g ∈ Z.ideal P.affOpen
  have h0 : P.secHom g = 0 := by
    simp only [AffPres.secHom, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.mpr hg, map_zero]
  rw [h0]
  exact zero_mem _

theorem AffPres.zero_bdIdeal_iff [LocallyOfFiniteType s] (P : AffPres s) (Z : W.IdealSheafData)
    (x : W) (hx : x ∈ P.V) (hc : IsClosed ({x} : Set W)) :
    (∀ g ∈ P.bdIdeal Z, eval (P.coord x hx) g = 0) ↔ x ∈ (Z.support : Set W) := by
  change _ ↔ x ∈ Z.support
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := P.affOpen) hx, Scheme.mem_zeroLocus_iff]
  constructor
  · intro h f hf
    obtain ⟨g, rfl⟩ := secHom_surjective P f
    have hz := (mem_zeroLocus_secHom_iff P x hx hc g).2 (h g hf)
    exact (Scheme.mem_zeroLocus_iff W {P.secHom g} x).1 hz _ rfl
  · intro h g hg
    apply (mem_zeroLocus_secHom_iff P x hx hc g).1
    rw [Scheme.mem_zeroLocus_iff]
    rintro f rfl
    exact h _ hg

theorem AffPres.exists_basicOpen_cover (P : AffPres s) (O : W.Opens) :
    ∃ T : Set (MvPolynomial (Fin P.n) ℂ), ∀ y ∈ P.V,
      (y ∈ O ↔ ∃ g ∈ T, y ∈ W.basicOpen (P.secHom g)) := by
  refine ⟨{g | W.basicOpen (P.secHom g) ≤ O}, fun y hy => ⟨fun hyO => ?_, ?_⟩⟩
  · obtain ⟨f, hf, hyf⟩ := P.isAffineOpen.exists_basicOpen_le (V := O) ⟨y, hyO⟩ hy
    obtain ⟨g, rfl⟩ := secHom_surjective P f
    exact ⟨g, hf, hyf⟩
  · rintro ⟨g, hg, hyg⟩
    exact hg hyg

theorem exists_sncData [IsNoetherian W] [LocallyOfFiniteType s] {Z : W.IdealSheafData}
    (hZ : FinalTheorems.Snc Z) (P : AffPres s) {rc : ℕ} (c : Fin rc ≃ comps (Z.support : Set W)) (e : ℕ)
    (x : W) (hx : x ∈ P.V) (hcl : IsClosed ({x} : Set W))
    (hdim : ringKrullDim (W.presheaf.stalk x) = e) :
    ∃ S : SncData P.K (P.bdIdeal Z) (P.coord x hx) e rc,
      (∀ l ∈ S.J, ∃ k, S.σ l = some k ∧ IsBranch (Z.support : Set W) (P.secHom (S.r l)) x (c k)) ∧
      ∃ O : W.Opens, x ∈ O ∧ O ≤ P.V ∧
      ∀ k (y : W) (hy : y ∈ P.V), y ∈ O → IsClosed ({y} : Set W) →
        (y ∈ (c k : Set W) ↔ ∃ l, S.σ l = some k ∧ eval (P.coord y hy) (S.r l) = 0) := by
  classical
  obtain ⟨hreg, U, hxU, n', f, J, hrsp, hZU⟩ := hZ x
  have hn : n' = e := by
    have h1 := hrsp.2
    rw [hdim] at h1
    exact_mod_cast h1
  subst hn
  have hV : IsAffineOpen P.V := P.isAffineOpen
  have hpK : ∀ h ∈ P.K, eval (P.coord x hx) h = 0 := P.eval_coord_eq_zero x hx hcl
  have hfrac := fun l => exists_mk_locRing P.K (P.coord x hx)
    (P.stalkEquiv x hx hcl (W.presheaf.germ U.1 x hxU (f l)))
  choose a b hb hab using hfrac
  have hgerm : ∀ l, W.presheaf.germ P.V x hx (P.secHom (a l)) =
      W.presheaf.germ U.1 x hxU (f l) * W.presheaf.germ P.V x hx (P.secHom (b l)) := by
    intro l
    apply (P.stalkEquiv x hx hcl).injective
    rw [map_mul, P.stalkEquiv_germ, P.stalkEquiv_germ]
    exact (hab l).symm
  have hbu : ∀ l, IsUnit (W.presheaf.germ P.V x hx (P.secHom (b l))) :=
    fun l => (germ_unit_iff P x hx hcl (b l)).mpr (hb l)
  have hbr := fun l (hl : l ∈ J) => existsUnique_branch x U hxU f J hrsp hZU l hl
  let B := fun l => if hl : l ∈ J then Classical.choose (hbr l hl).exists else (∅ : Set W)
  have hB : ∀ l (hl : l ∈ J), IsBranch (Z.support : Set W) (f l) x (B l) := by
    intro l hl
    simp only [B, dif_pos hl]
    exact Classical.choose_spec (hbr l hl).exists
  have hBu : ∀ l (hl : l ∈ J) C, IsBranch (Z.support : Set W) (f l) x C → C = B l :=
    fun l hl C hC => (hbr l hl).unique hC (hB l hl)
  let σ := fun l => if hl : l ∈ J then some (c.symm ⟨B l, (hB l hl).1⟩) else none
  have hσ : ∀ l k, σ l = some k ↔ l ∈ J ∧ IsBranch (Z.support : Set W) (f l) x (c k) := by
    intro l k
    by_cases hl : l ∈ J
    · simp only [σ, dif_pos hl, Option.some.injEq]
      constructor
      · intro h
        refine ⟨hl, ?_⟩
        have : c k = ⟨B l, (hB l hl).1⟩ := by rw [← h]; simp
        rw [this]
        exact hB l hl
      · rintro ⟨-, hbk⟩
        have : (⟨B l, (hB l hl).1⟩ : comps (Z.support : Set W)) = c k :=
          Subtype.ext (hBu l hl _ hbk).symm
        rw [this]
        simp
    · simp only [σ, dif_neg hl]
      simp [hl]
  have hinj : Set.InjOn σ J := by
    intro l hl l' hl' h
    have hl₁ : l ∈ J := hl
    have hl₁' : l' ∈ J := hl'
    by_contra hne
    obtain ⟨k, hk⟩ : ∃ k, σ l = some k := ⟨c.symm ⟨B l, (hB l hl₁).1⟩, by simp only [σ, dif_pos hl₁]⟩
    have h1 := ((hσ l k).mp hk).2
    have h2 := ((hσ l' k).mp (h.symm.trans hk)).2
    exact branch_ne x U hxU f J hrsp hZU hl₁ hl₁' hne h1 h2 rfl
  have hnone : ∀ l, σ l = none ↔ l ∉ J := by
    intro l
    by_cases hl : l ∈ J <;> simp [σ, hl]
  have hspan : Ideal.span (Set.range fun l => algebraMap _ (locRing P.K (P.coord x hx)) (a l)) =
      Ideal.map (algebraMap _ (locRing P.K (P.coord x hx))) (ptIdeal (P.coord x hx)) := by
    have hr := ((P.rsp_iff x hx hcl (fun l => W.presheaf.germ U.1 x hxU (f l))).mp hrsp).1
    rw [← hr]
    exact span_range_eq_of_mul_unit _ _ (fun l => algebraMap _ _ (b l))
      (fun l => (isUnit_algebraMap_locRing_iff _ _ hpK _).mpr (hb l)) hab

  have hst : (Z.ideal P.affOpen).map (W.presheaf.germ P.V x hx).hom =
      Ideal.span {W.presheaf.germ U.1 x hxU (∏ i ∈ J, f i)} := by
    have h := stalkIdeal_eq Z U P.affOpen x hxU hx
    rw [hZU, Ideal.map_span, Set.image_singleton] at h
    exact h
  have e1 : W.presheaf.germ P.V x hx (P.secHom (∏ l ∈ J, a l)) =
      W.presheaf.germ U.1 x hxU (∏ i ∈ J, f i) *
        ∏ l ∈ J, W.presheaf.germ P.V x hx (P.secHom (b l)) := by
    simp only [map_prod, hgerm, Finset.prod_mul_distrib]
  have hprod : P.stalkEquiv x hx hcl (W.presheaf.germ U.1 x hxU (∏ i ∈ J, f i)) *
      algebraMap _ (locRing P.K (P.coord x hx)) (∏ l ∈ J, b l) =
        algebraMap _ (locRing P.K (P.coord x hx)) (∏ l ∈ J, a l) := by
    simp only [map_prod, ← Finset.prod_mul_distrib, hab]
  obtain ⟨hh, heval, hmbd, hlesp⟩ :=
    exists_den P x hx hcl hV (Z.ideal P.affOpen) J a b hb _ hst e1 hprod

  obtain ⟨O₁, hxO₁, -, hO₁⟩ := exists_open_comps x U hxU f J hrsp hZU
  have hnb := fun l => exists_nbhd_zeroLocus hxU hx (f l) (P.secHom (a l)) _ (hbu l) (hgerm l)
  choose O' hxO' hO' using hnb
  let Oset : Set W := (O₁ : Set W) ∩ P.V ∩ ⋂ l, (O' l : Set W)
  have hOo : IsOpen Oset :=
    (O₁.isOpen.inter P.V.isOpen).inter (isOpen_iInter_of_finite fun l => (O' l).isOpen)
  refine ⟨⟨a, J, hh, σ, hinj, hnone, hspan, heval, hmbd, hlesp⟩, ?_,
    ⟨Oset, hOo⟩, ⟨⟨hxO₁, hx⟩, Set.mem_iInter.mpr hxO'⟩, fun z hz => hz.1.2, ?_⟩
  · intro l hl
    have hl' : l ∈ J := hl
    refine ⟨c.symm ⟨B l, (hB l hl').1⟩, by show σ l = _; simp only [σ, dif_pos hl'], ?_⟩
    rw [Equiv.apply_symm_apply]
    exact isBranch_of_germ Z.support.isClosed hxU hx (hB l hl') _ (hgerm l)
  · intro k y hy hyO hcy
    have hyO' : y ∈ Oset := hyO
    have e2 : ∀ l, eval (P.coord y hy) (a l) = 0 ↔ y ∈ W.zeroLocus {f l} := by
      intro l
      rw [← mem_zeroLocus_secHom_iff P y hy hcy, hO' l y (Set.mem_iInter.mp hyO'.2 l)]
    have e1 : y ∈ (c k : Set W) ↔ y ∈ (c k : Set W) ∩ (O₁ : Set W) :=
      ⟨fun h => ⟨h, hyO'.1.1⟩, fun h => h.1⟩
    rw [e1, hO₁ (c k) (c k).2]
    show (y ∈ (O₁ : Set W) ∧ ∃ i ∈ J, IsBranch (Z.support : Set W) (f i) x (c k) ∧
      y ∈ W.zeroLocus {f i}) ↔ ∃ l, σ l = some k ∧ eval (P.coord y hy) (a l) = 0
    constructor
    · rintro ⟨-, i, hi, hbi, hyi⟩
      exact ⟨i, (hσ i k).mpr ⟨hi, hbi⟩, (e2 i).mpr hyi⟩
    · rintro ⟨l, hl, hev⟩
      obtain ⟨hlJ, hbl⟩ := (hσ l k).mp hl
      exact ⟨hyO'.1.1, l, hlJ, hbl, (e2 l).mp hev⟩

end Chart

end

end ReciprocityTheory.AnForm.R
