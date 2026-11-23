import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleSpan

open ReciprocityTheory.ChartRestriction.G.H1 ReciprocityTheory.ChartRestriction.G.DVR

variable {X X' Y Y' Z : Scheme.{0}}

theorem gs_sub' (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (a b : Γ(X, U)) :
    gs r z U (a - b) = gs r z U a - gs r z U b := by simp only [gs_eq r z U h, map_sub]

theorem gs_sum' (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) {ι : Type} [Fintype ι]
    (a : ι → Γ(X, U)) : gs r z U (∑ i, a i) = ∑ i, gs r z U (a i) := by
  simp only [gs_eq r z U h, map_sum]

theorem gs_one' (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) : gs r z U 1 = 1 := by
  simp only [gs_eq r z U h, map_one]

theorem isUnit_gs_iff (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (a : Γ(X, U)) :
    IsUnit (gs r z U a) ↔ r z ∈ X.basicOpen a := by
  rw [gs_eq r z U h]
  refine ((Z.mem_basicOpen ((r.app U).hom a) z h).symm).trans ?_
  rw [← Scheme.Hom.preimage_basicOpen]
  rfl

theorem mem_nonzeroLocus_iff_gs {H : LB X} (t : LB.Sec H) (r : Z ⟶ X) (z : Z) {k : H.ι}
    (hk : r z ∈ H.U k) : r z ∈ nonzeroLocus t ↔ IsUnit (gs r z _ (t.f k)) := by
  rw [isUnit_gs_iff r z _ hk]
  refine ⟨fun h => ?_, fun h => Opens.mem_iSup.2 ⟨k, h⟩⟩
  obtain ⟨j, hj⟩ := Opens.mem_iSup.1 h
  have hj' : r z ∈ H.U j := X.basicOpen_le _ hj
  rw [← isUnit_gs_iff r z _ hk, gs_compat t r z hk hj']
  exact (Units.isUnit _).mul ((isUnit_gs_iff r z _ hj' _).2 hj)

theorem exists_chart_of_mem {H : LB X} (t : LB.Sec H) {x : X} (h : x ∈ nonzeroLocus t) :
    ∃ k, x ∈ H.U k := by
  obtain ⟨j, hj⟩ := Opens.mem_iSup.1 h
  exact ⟨j, X.basicOpen_le _ hj⟩

def IsRatio {H : LB X} (s t : LB.Sec H) (r : Γ(X, nonzeroLocus t)) : Prop :=
  ∀ k, resG X (inf_le_right : nonzeroLocus t ⊓ H.U k ≤ H.U k) (s.f k) =
    resG X (inf_le_left : nonzeroLocus t ⊓ H.U k ≤ nonzeroLocus t) r *
      resG X (inf_le_right : nonzeroLocus t ⊓ H.U k ≤ H.U k) (t.f k)

theorem IsRatio.gs {H : LB X} {s t : LB.Sec H} {r : Γ(X, nonzeroLocus t)} (h : IsRatio s t r)
    (ρ : Z ⟶ X) (z : Z) {k : H.ι} (ht : ρ z ∈ nonzeroLocus t) (hk : ρ z ∈ H.U k) :
    gs ρ z _ (s.f k) = gs ρ z _ r * gs ρ z _ (t.f k) := by
  have hm : ρ z ∈ nonzeroLocus t ⊓ H.U k := ⟨ht, hk⟩
  have e := congrArg (Geo.Tor.gs ρ z _) (h k)
  rwa [gs_res _ z _ hm, gs_mul _ z _ hm, gs_res _ z _ hm, gs_res _ z _ hm] at e

theorem isRatio_of_gs {H : LB X} {s t : LB.Sec H} {r : Γ(X, nonzeroLocus t)}
    (h : ∀ x ∈ nonzeroLocus t, ∃ k, x ∈ H.U k ∧
      gs (𝟙 X) x _ (s.f k) = gs (𝟙 X) x _ r * gs (𝟙 X) x _ (t.f k)) : IsRatio s t r := by
  intro k
  refine fn_ext fun x hx => ?_
  obtain ⟨j, hj, e⟩ := h x hx.1
  rw [gs_res _ x _ hx, gs_mul _ x _ hx, gs_res _ x _ hx, gs_res _ x _ hx,
    gs_compat s (𝟙 X) x hx.2 hj, gs_compat t (𝟙 X) x hx.2 hj, e]
  ring

theorem IsRatio.unique {H : LB X} {s t : LB.Sec H} {r r' : Γ(X, nonzeroLocus t)}
    (h : IsRatio s t r) (h' : IsRatio s t r') : r = r' := by
  refine fn_ext fun x hx => ?_
  obtain ⟨k, hk⟩ := exists_chart_of_mem t hx
  exact ((mem_nonzeroLocus_iff_gs t (𝟙 X) x hk).1 hx).mul_right_cancel
    ((h.gs (𝟙 X) x hx hk).symm.trans (h'.gs (𝟙 X) x hx hk))

theorem exists_isRatio {H : LB X} (s t : LB.Sec H) : ∃ r, IsRatio s t r := by
  have hu : ∀ k, IsUnit (resG X (X.basicOpen_le (t.f k)) (t.f k)) := fun k =>
    X.toRingedSpace.isUnit_res_basicOpen (t.f k)
  obtain ⟨u, hu⟩ : ∃ u : ∀ k, Γ(X, X.basicOpen (t.f k)), ∀ k x, x ∈ X.basicOpen (t.f k) →
      gs (𝟙 X) x _ (s.f k) = gs (𝟙 X) x _ (u k) * gs (𝟙 X) x _ (t.f k) := by
    refine ⟨fun k => resG X (X.basicOpen_le (t.f k)) (s.f k) * ((hu k).unit⁻¹).val, fun k x hx => ?_⟩
    rw [← gs_res (𝟙 X) x (X.basicOpen_le (t.f k)) hx (t.f k), ← gs_mul _ x _ hx, mul_assoc,
      IsUnit.val_inv_mul, mul_one, gs_res _ x _ hx]
  obtain ⟨a, ha, -⟩ := X.sheaf.existsUnique_gluing' (fun k => X.basicOpen (t.f k)) (nonzeroLocus t)
    (fun k => homOfLE (le_iSup (fun k => X.basicOpen (t.f k)) k)) le_rfl u
    (fun j k => fn_ext (V := X.basicOpen (t.f j) ⊓ X.basicOpen (t.f k)) fun y hy => by
      refine (gs_res (𝟙 X) y inf_le_left hy _).trans
        (Eq.trans ?_ (gs_res (𝟙 X) y inf_le_right hy _).symm)
      have hj : (𝟙 X : X ⟶ X) y ∈ H.U j := X.basicOpen_le _ hy.1
      have hk : (𝟙 X : X ⟶ X) y ∈ H.U k := X.basicOpen_le _ hy.2
      refine ((isUnit_gs_iff (𝟙 X) y _ hj _).2 hy.1).mul_right_cancel ?_
      rw [← hu j y hy.1, gs_compat s (𝟙 X) y hj hk, gs_compat t (𝟙 X) y hj hk, hu k y hy.2]
      ring)
  refine ⟨a, isRatio_of_gs fun x hx => ?_⟩
  obtain ⟨k, hk⟩ := Opens.mem_iSup.1 hx
  refine ⟨k, X.basicOpen_le _ hk, (hu k x hk).trans ?_⟩
  rw [← ha k]
  exact congrArg (· * _) (gs_res (𝟙 X) x (le_iSup (fun k => X.basicOpen (t.f k)) k) hk a)

theorem IsRatio.basicOpen {H : LB X} {s t : LB.Sec H} {r : Γ(X, nonzeroLocus t)}
    (h : IsRatio s t r) : X.basicOpen r = nonzeroLocus t ⊓ nonzeroLocus s := by
  ext x
  have key : x ∈ nonzeroLocus t → (x ∈ X.basicOpen r ↔ x ∈ nonzeroLocus s) := fun hx => by
    obtain ⟨k, hk⟩ := exists_chart_of_mem t hx
    refine (isUnit_gs_iff (𝟙 X) x _ hx r).symm.trans
      (Iff.trans ?_ (mem_nonzeroLocus_iff_gs s (𝟙 X) x hk).symm)
    rw [h.gs (𝟙 X) x hx hk, IsUnit.mul_iff]
    exact ⟨fun e => ⟨e, (mem_nonzeroLocus_iff_gs t (𝟙 X) x hk).1 hx⟩, fun e => e.1⟩
  exact ⟨fun hx => ⟨X.basicOpen_le _ hx, (key (X.basicOpen_le _ hx)).1 hx⟩,
    fun hx => (key hx.1).2 hx.2⟩

def EmbedsBy (f : X ⟶ Y) {H : LB X} {ι : Type} (s : ι → LB.Sec H) : Prop :=
  (⨆ i, nonzeroLocus (s i) = ⊤) ∧ ∀ i, IsAffineOpen (nonzeroLocus (s i)) ∧
    ∃ r : ι → Γ(X, nonzeroLocus (s i)), (∀ j, IsRatio (s j) (s i) (r j)) ∧
      Function.Surjective (MvPolynomial.eval₂Hom (f.appLE ⊤ (nonzeroLocus (s i)) le_top).hom r)

def InSpan (f : X ⟶ Y) {H : LB X} {ι : Type} [Fintype ι] (t : ι → LB.Sec H) (s : LB.Sec H) : Prop :=
  ∃ c : ι → Γ(Y, ⊤), ∀ k, s.f k = ∑ l, (f.appLE ⊤ (H.U k) le_top).hom (c l) * (t l).f k

theorem veryAmpleAt_iff {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) (N : ℕ) :
    VeryAmpleAt A L N ↔ ∀ U : S.Opens, IsAffineOpen U →
      ∃ M : ℕ, ∃ s : Fin (M + 1) → LB.Sec (powOver A L U N), EmbedsBy (A.hom ∣_ U) s := Iff.rfl

theorem gs_const (f : X ⟶ Y) (W : X.Opens) (r : Z ⟶ X) (z : Z) (h : r z ∈ W) (b : Γ(Y, ⊤)) :
    gs r z W ((f.appLE ⊤ W le_top).hom b) = gs (r ≫ f) z ⊤ b := gs_appLE f ⊤ W le_top r z h b

theorem mem_top' (x : X) : x ∈ (⊤ : X.Opens) := trivial

theorem isoSpec_inv_appTop [IsAffine Y] : Y.isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ(Y, ⊤)).inv := by
  rw [← cancel_mono (Scheme.ΓSpecIso Γ(Y, ⊤)).hom, Iso.inv_hom_id, ← Scheme.toSpecΓ_appTop,
    ← Scheme.Hom.comp_appTop]
  exact (congrArg Scheme.Hom.appTop Y.isoSpec.hom_inv_id).trans Scheme.Hom.id_appTop

theorem exists_hom_spec (f : X ⟶ Y) [IsAffine Y] (D : X.Opens) (P : CommRingCat.{0})
    (C : Γ(Y, ⊤) ⟶ P) (ψ : P ⟶ Γ(X, D)) (h : C ≫ ψ = f.appLE ⊤ D le_top) :
    ∃ q : D.toScheme ⟶ Spec P, D.ι ≫ f = q ≫ Spec.map C ≫ Y.isoSpec.inv ∧
      ∀ z a, gs q z ⊤ ((Scheme.ΓSpecIso P).inv.hom a) = gs D.ι z D (ψ.hom a) := by
  refine ⟨D.toSpecΓ ≫ Spec.map ψ, ?_, fun z a => ?_⟩
  · rw [Category.assoc, ← Spec.map_comp_assoc, h, ← Category.assoc, Iso.eq_comp_inv]
    rw [Category.assoc]
    change D.ι ≫ f ≫ Y.toSpecΓ = D.toSpecΓ ≫ Spec.map (f.appTop ≫ X.presheaf.map (homOfLE le_top).op)
    rw [Spec.map_comp, Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top_assoc, Scheme.toSpecΓ_naturality]
  · have e : (D.toSpecΓ ≫ Spec.map ψ).appTop.hom ((Scheme.ΓSpecIso P).inv.hom a) =
        D.topIso.inv.hom (ψ.hom a) := by
      change ((Scheme.ΓSpecIso P).inv ≫ (D.toSpecΓ ≫ Spec.map ψ).appTop).hom a = (ψ ≫ D.topIso.inv).hom a
      rw [Scheme.Hom.comp_appTop, ← Scheme.ΓSpecIso_inv_naturality_assoc, Scheme.Opens.toSpecΓ_appTop,
        Iso.inv_hom_id_assoc]
    have hz : D.ι z ∈ D := z.2
    have e' : D.topIso.inv = D.ι.appLE D ⊤ (fun x _ => x.2) := by
      exact (Scheme.Opens.ι_appLE D D ⊤ _).symm
    have e₁ := gs_appLE D.ι D ⊤ (fun x _ => x.2) (𝟙 _) z trivial (ψ.hom a)
    have e₂ := gs_pull (𝟙 _) (D.toSpecΓ ≫ Spec.map ψ) z ⊤ trivial ((Scheme.ΓSpecIso P).inv.hom a)
    rw [Category.id_comp] at e₁ e₂
    rw [← e₁, ← e₂, ← e', ← e]
    rfl

theorem ker_sup_span_eq_top (f : X ⟶ Y) [IsAffine Y] [UniversallyClosed f] {H : LB X} {ι κ : Type}
    [Fintype ι] (t : ι → LB.Sec H) (s : κ → LB.Sec H) (hcov : ⨆ j, nonzeroLocus (s j) = ⊤)
    (c : κ → ι → Γ(Y, ⊤))
    (hc : ∀ j k, (s j).f k = ∑ l, (f.appLE ⊤ (H.U k) le_top).hom (c j l) * (t l).f k)
    (t₀ : LB.Sec H) (hD : IsCompact (nonzeroLocus t₀ : Set X)) (r : ι → Γ(X, nonzeroLocus t₀))
    (hr : ∀ l, IsRatio (t l) t₀ (r l)) :
    RingHom.ker (MvPolynomial.eval₂Hom (f.appLE ⊤ (nonzeroLocus t₀) le_top).hom r) ⊔
      Ideal.span (Set.range fun j => ∑ l, MvPolynomial.C (c j l) * MvPolynomial.X l) = ⊤ := by
  let P : CommRingCat.{0} := .of (MvPolynomial ι Γ(Y, ⊤))
  let C : Γ(Y, ⊤) ⟶ P := CommRingCat.ofHom MvPolynomial.C
  let ψ : P ⟶ Γ(X, nonzeroLocus t₀) :=
    CommRingCat.ofHom (MvPolynomial.eval₂Hom (f.appLE ⊤ (nonzeroLocus t₀) le_top).hom r)
  obtain ⟨q, hq, hq'⟩ := exists_hom_spec f (nonzeroLocus t₀) P C ψ
    (CommRingCat.hom_ext (RingHom.ext fun b => MvPolynomial.eval₂Hom_C _ _ b))
  let g : Spec P ⟶ Y := Spec.map C ≫ Y.isoSpec.inv
  let e : P →+* Γ(Spec P, ⊤) := (Scheme.ΓSpecIso P).inv.hom
  have hg : ∀ b, (g.app ⊤).hom b = e (MvPolynomial.C b) := fun b => by
    change g.appTop.hom b = (C ≫ (Scheme.ΓSpecIso P).inv).hom b
    rw [Scheme.ΓSpecIso_inv_naturality, Scheme.Hom.comp_appTop]
    rw [isoSpec_inv_appTop]
  let p₁ := pullback.fst f g
  let p₂ := pullback.snd f g
  let d : ∀ (k : H.ι) (l : ι), Γ(pullback f g, p₁ ⁻¹ᵁ H.U k) := fun k l =>
    (p₁.app _).hom ((t l).f k) -
      (p₂.appLE ⊤ _ le_top).hom (e (MvPolynomial.X l)) * (p₁.app _).hom (t₀.f k)
  have hd : ∀ (Z : Scheme.{0}) (ρ : Z ⟶ pullback f g) (z : Z) k l, p₁ (ρ z) ∈ H.U k →
      gs ρ z _ (d k l) = gs (ρ ≫ p₁) z _ ((t l).f k) -
        gs (ρ ≫ p₂) z ⊤ (e (MvPolynomial.X l)) * gs (ρ ≫ p₁) z _ (t₀.f k) := fun Z ρ z k l h => by
    have h' : ρ z ∈ p₁ ⁻¹ᵁ H.U k := h
    rw [gs_sub' _ _ _ h', gs_mul _ _ _ h', gs_pull _ _ _ _ h, gs_pull _ _ _ _ h, gs_const _ _ _ _ h']
  let O : (pullback f g).Opens := ⨆ kl : H.ι × ι, (pullback f g).basicOpen (d kl.1 kl.2)
  have hC : IsClosed (p₂ '' (O : Set (pullback f g : Scheme))ᶜ) := p₂.isClosedMap _ O.isOpen.isClosed_compl
  have h₁ : ∀ z, q z ∈ p₂ '' (O : Set (pullback f g : Scheme))ᶜ := fun z => by
    let γ := pullback.lift _ _ hq
    have e₁ : γ ≫ p₁ = (nonzeroLocus t₀).ι := pullback.lift_fst _ _ _
    have e₂ : γ ≫ p₂ = q := pullback.lift_snd _ _ _
    refine ⟨γ z, fun hz => ?_, by rw [← e₂]; rfl⟩
    obtain ⟨⟨k, l⟩, hkl⟩ := Opens.mem_iSup.1 hz
    have hk : γ z ∈ p₁ ⁻¹ᵁ H.U k := (pullback f g).basicOpen_le _ hkl
    have hk' : (nonzeroLocus t₀).ι z ∈ H.U k := by rw [← e₁]; exact hk
    have u := (isUnit_gs_iff γ z _ hk _).2 hkl
    rw [hd _ γ z k l hk, e₁, e₂, hq', (hr l).gs _ z z.2 hk'] at u
    have e₃ : ψ.hom (MvPolynomial.X l) = r l := MvPolynomial.eval₂Hom_X' _ _ l
    rw [e₃, sub_self] at u
    exact not_isUnit_zero u
  by_contra hne
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  let x : Spec P := (⟨m, hm.isPrime⟩ : PrimeSpectrum P)
  have hx : x ∈ p₂ '' (O : Set (pullback f g : Scheme))ᶜ := by
    by_contra hx
    obtain ⟨_, ⟨a, rfl⟩, ha, hsub⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hx hC.isOpen_compl
    have hn : IsNilpotent (ψ.hom a) := by
      rw [Scheme.isNilpotent_iff_basicOpen_eq_bot_of_isCompact hD, eq_bot_iff]
      intro y hy
      let z : (nonzeroLocus t₀).toScheme := ⟨y, X.basicOpen_le _ hy⟩
      have u := (isUnit_gs_iff (nonzeroLocus t₀).ι z _ z.2 _).2 hy
      rw [← hq', isUnit_gs_iff _ _ _ (mem_top' _)] at u
      refine (hsub ?_ (h₁ z)).elim
      exact (basicOpen_eq_of_affine (R := P) a).le u
    obtain ⟨n, hn⟩ := hn
    refine ha (hm.isPrime.mem_of_pow_mem n (hle (Ideal.mem_sup_left ?_)))
    exact (map_pow _ _ _).trans hn
  obtain ⟨z, hz, hzx⟩ := hx
  obtain ⟨j, hj⟩ := Opens.mem_iSup.1 (show p₁ z ∈ ⨆ j, nonzeroLocus (s j) by rw [hcov]; trivial)
  obtain ⟨k, hk⟩ := exists_chart_of_mem _ hj
  have u := (mem_nonzeroLocus_iff_gs (s j) p₁ z hk).1 hj
  have nu : ∀ l, gs p₁ z _ ((t l).f k) - gs p₂ z ⊤ (e (MvPolynomial.X l)) * gs p₁ z _ (t₀.f k) ∈
      IsLocalRing.maximalIdeal _ := fun l hu => by
    have := hd _ (𝟙 _) z k l hk
    rw [Category.id_comp, Category.id_comp] at this
    rw [← this, isUnit_gs_iff (𝟙 _) z _ hk] at hu
    exact hz (Opens.mem_iSup.2 ⟨(k, l), hu⟩)
  have nl : gs p₂ z ⊤ (e (∑ l, MvPolynomial.C (c j l) * MvPolynomial.X l)) ∈
      IsLocalRing.maximalIdeal _ := fun hu => by
    rw [isUnit_gs_iff _ _ _ (mem_top' _), hzx] at hu
    exact (basicOpen_eq_of_affine (R := P) _).le hu
      (hle (Ideal.mem_sup_right (Ideal.subset_span ⟨j, rfl⟩)))
  have hb : ∀ b, gs p₁ z _ ((f.appLE ⊤ (H.U k) le_top).hom b) = gs p₂ z ⊤ (e (MvPolynomial.C b)) :=
    fun b => by
      rw [gs_const _ _ _ _ hk, ← hg, pullback.condition]
      exact (gs_pull p₂ g z ⊤ trivial b).symm
  have key : gs p₁ z _ ((s j).f k) = ∑ l, gs p₂ z ⊤ (e (MvPolynomial.C (c j l))) *
      (gs p₁ z _ ((t l).f k) - gs p₂ z ⊤ (e (MvPolynomial.X l)) * gs p₁ z _ (t₀.f k)) +
      gs p₂ z ⊤ (e (∑ l, MvPolynomial.C (c j l) * MvPolynomial.X l)) * gs p₁ z _ (t₀.f k) := by
    rw [hc, gs_sum' _ _ _ hk, map_sum, gs_sum' _ _ _ (mem_top' _), Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [gs_mul _ _ _ hk, hb, map_mul, gs_mul _ _ _ (mem_top' _)]
    ring
  rw [key] at u
  exact (Ideal.add_mem _ (Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (nu l))
    (Ideal.mul_mem_right _ _ nl)) u

theorem isCompact_nonzeroLocus {H : LB X} {κ : Type} [Finite κ] (s : κ → LB.Sec H)
    (hcov : ⨆ j, nonzeroLocus (s j) = ⊤) (haff : ∀ j, IsAffineOpen (nonzeroLocus (s j)))
    (t₀ : LB.Sec H) : IsCompact (nonzeroLocus t₀ : Set X) := by
  have e : nonzeroLocus t₀ = ⨆ j, nonzeroLocus (s j) ⊓ nonzeroLocus t₀ := by
    rw [← iSup_inf_eq, hcov, top_inf_eq]
  rw [e, Opens.coe_iSup]
  refine isCompact_iUnion fun j => ?_
  obtain ⟨σ, hσ⟩ := exists_isRatio t₀ (s j)
  rw [← hσ.basicOpen]
  exact ((haff j).basicOpen σ).isCompact

theorem EmbedsBy.affine_and_surjective {f : X ⟶ Y} [IsAffine Y] [UniversallyClosed f] {H : LB X}
    {ι κ : Type} [Fintype ι] [Finite κ] {s : κ → LB.Sec H} (hs : EmbedsBy f s) {t : ι → LB.Sec H}
    (hst : ∀ j, InSpan f t (s j)) (t₀ : LB.Sec H) :
    IsAffineOpen (nonzeroLocus t₀) ∧ ∀ r : ι → Γ(X, nonzeroLocus t₀),
      (∀ l, IsRatio (t l) t₀ (r l)) → Function.Surjective
        (MvPolynomial.eval₂Hom (f.appLE ⊤ (nonzeroLocus t₀) le_top).hom r) := by
  obtain ⟨hcov, hs⟩ := hs
  choose haff rs hrs hsurj using hs
  choose c hc using hst
  have hD := isCompact_nonzeroLocus s hcov haff t₀
  choose σ hσ using fun j => exists_isRatio t₀ (s j)
  have main : ∀ r : ι → Γ(X, nonzeroLocus t₀), (∀ l, IsRatio (t l) t₀ (r l)) →
      IsAffineOpen (nonzeroLocus t₀) ∧ Function.Surjective
        (MvPolynomial.eval₂Hom (f.appLE ⊤ (nonzeroLocus t₀) le_top).hom r) := by
    intro r hr
    have top := ker_sup_span_eq_top f t s hcov c hc t₀ hD r hr
    set ψ := MvPolynomial.eval₂Hom (f.appLE ⊤ (nonzeroLocus t₀) le_top).hom r with hψ
    set lam : κ → MvPolynomial ι Γ(Y, ⊤) := fun j => ∑ l, MvPolynomial.C (c j l) * MvPolynomial.X l
      with hlam
    have hρ : ∀ j, IsRatio (s j) t₀ (ψ (lam j)) := fun j => isRatio_of_gs fun x hx => by
      obtain ⟨k, hk⟩ := exists_chart_of_mem t₀ hx
      refine ⟨k, hk, ?_⟩
      rw [hc, gs_sum' (𝟙 X) x _ hk, hlam, map_sum, gs_sum' (𝟙 X) x _ hx, Finset.sum_mul]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_mul, hψ, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X', gs_mul (𝟙 X) x _ hk,
        gs_mul (𝟙 X) x _ hx, gs_const f _ (𝟙 X) x hk, gs_const f _ (𝟙 X) x hx,
        (hr l).gs (𝟙 X) x hx hk, mul_assoc]
    have hbo : ∀ j, X.basicOpen (ψ (lam j)) = X.basicOpen (σ j) := fun j => by
      rw [(hρ j).basicOpen, (hσ j).basicOpen, inf_comm]
    have hA : IsAffineOpen (nonzeroLocus t₀) := by
      refine isAffineOpen_of_isAffineOpen_basicOpen _ (Set.range fun j => ψ (lam j)) ?_ ?_
      · have := congrArg (Ideal.map ψ) top
        rw [Ideal.map_sup, Ideal.map_top, Ideal.map_span, ← Set.range_comp,
          (Ideal.map_eq_bot_iff_le_ker ψ).2 le_rfl, bot_sup_eq] at this
        exact this
      · rintro _ ⟨j, rfl⟩
        rw [hbo]
        exact (haff j).basicOpen _
    refine ⟨hA, fun x₀ => ?_⟩
    have loc : ∀ j, ∃ n, ψ (lam j) ^ n * x₀ ∈ ψ.range := fun j => by
      have hV : X.basicOpen (σ j) ≤ nonzeroLocus t₀ := (hbo j).ge.trans (X.basicOpen_le _)
      have hV' : X.basicOpen (σ j) ≤ nonzeroLocus (s j) := X.basicOpen_le _
      let θ : MvPolynomial ι Γ(Y, ⊤) →+* Γ(X, X.basicOpen (σ j)) := (resG X hV).comp ψ
      have rat : ∀ (w : LB.Sec H) (a : Γ(X, nonzeroLocus (s j))) (b : Γ(X, nonzeroLocus t₀)),
          IsRatio w (s j) a → IsRatio w t₀ b → θ (lam j) * resG X hV' a = resG X hV b :=
        fun w a b ha hb => fn_ext fun x hx => by
          obtain ⟨k, hk⟩ := exists_chart_of_mem t₀ (hV hx)
          refine ((mem_nonzeroLocus_iff_gs t₀ (𝟙 X) x hk).1 (hV hx)).mul_right_cancel ?_
          rw [gs_mul (𝟙 X) x _ hx, gs_res (𝟙 X) x _ hx, gs_res (𝟙 X) x _ hx,
            ← hb.gs (𝟙 X) x (hV hx) hk, ha.gs (𝟙 X) x (hV' hx) hk, (hρ j).gs (𝟙 X) x (hV hx) hk]
          have : gs (𝟙 X) x _ (θ (lam j)) = gs (𝟙 X) x _ (ψ (lam j)) := gs_res (𝟙 X) x hV hx _
          rw [this]; ring
      have one : θ (lam j) * resG X hV' (σ j) = 1 :=
        (rat t₀ (σ j) 1 (hσ j) (fun k => by rw [map_one, one_mul])).trans (map_one _)
      have poly : ∀ p, ∃ n a, θ (lam j) ^ n * resG X hV' (MvPolynomial.eval₂Hom
          (f.appLE ⊤ (nonzeroLocus (s j)) le_top).hom (rs j) p) = θ a := fun p => by
        induction p using MvPolynomial.induction_on with
        | C b =>
          refine ⟨0, MvPolynomial.C b, fn_ext fun x hx => ?_⟩
          rw [pow_zero, one_mul, MvPolynomial.eval₂Hom_C, gs_res (𝟙 X) x _ hx,
            gs_const f _ (𝟙 X) x (hV' hx)]
          refine Eq.symm ((gs_res (𝟙 X) x hV hx _).trans ?_)
          rw [hψ, MvPolynomial.eval₂Hom_C, gs_const f _ (𝟙 X) x (hV hx)]
        | add p q hp hq =>
          obtain ⟨n, a, ha⟩ := hp
          obtain ⟨m, b, hb⟩ := hq
          refine ⟨n + m, lam j ^ m * a + lam j ^ n * b, ?_⟩
          rw [map_add, map_add, map_add, map_mul, map_mul, map_pow, map_pow, ← ha, ← hb]
          ring
        | mul_X p i hp =>
          obtain ⟨n, a, ha⟩ := hp
          refine ⟨n + 1, a * lam i, ?_⟩
          have e : θ (lam j) * resG X hV' (rs j i) = θ (lam i) := rat (s i) _ _ (hrs j i) (hρ i)
          rw [map_mul, map_mul, map_mul, MvPolynomial.eval₂Hom_X', ← ha, ← e]
          ring
      haveI := (haff j).isLocalization_basicOpen (σ j)
      obtain ⟨m, y, hy⟩ := IsLocalization.Away.surj (σ j) (resG X hV x₀)
      obtain ⟨p, rfl⟩ := hsurj j y
      obtain ⟨n, a, ha⟩ := poly p
      have hy' : resG X hV x₀ * resG X hV' (σ j) ^ m = resG X hV' (MvPolynomial.eval₂Hom
          (f.appLE ⊤ (nonzeroLocus (s j)) le_top).hom (rs j) p) := hy
      have z : resG X hV (ψ (lam j) ^ n * x₀ - ψ (lam j ^ m * a)) = 0 := by
        change (resG X hV) (_ - _) = 0
        rw [map_sub, map_mul, map_pow]
        change θ (lam j) ^ n * _ - θ (lam j ^ m * a) = 0
        rw [map_mul, map_pow, ← ha, ← hy']
        have := congrArg (· ^ m) one
        simp only [mul_pow, one_pow] at this
        linear_combination (-(θ (lam j) ^ n * resG X hV x₀)) * this
      obtain ⟨k, hk⟩ := exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen X hA
        (ψ (lam j) ^ n * x₀ - ψ (lam j ^ m * a)) (ψ (lam j)) (fn_ext fun x hx => by
          have hx' : x ∈ X.basicOpen (σ j) := (hbo j).le hx
          have e := congrArg (gs (𝟙 X) x _) z
          rw [gs_res (𝟙 X) x _ hx'] at e
          refine (gs_res (𝟙 X) x (X.basicOpen_le _) hx _).trans (e.trans ?_)
          simp only [gs_eq (𝟙 X) x _ hx, gs_eq (𝟙 X) x _ hx', map_zero])
      refine ⟨k + n, lam j ^ k * (lam j ^ m * a), ?_⟩
      rw [map_mul ψ (lam j ^ k), map_pow]
      linear_combination -hk
    letI : Algebra (MvPolynomial ι Γ(Y, ⊤)) Γ(X, nonzeroLocus t₀) := ψ.toAlgebra
    have := Submodule.mem_of_span_eq_top_of_smul_pow_mem
      (LinearMap.range (Algebra.linearMap (MvPolynomial ι Γ(Y, ⊤)) Γ(X, nonzeroLocus t₀)))
      ((RingHom.ker ψ : Set _) ∪ Set.range lam) (by rw [Ideal.span_union, Ideal.span_eq]; exact top) x₀ (by
        rintro ⟨a, ha | ⟨j, rfl⟩⟩
        · refine ⟨1, 0, ?_⟩
          change ψ 0 = ψ (a ^ 1) * x₀
          rw [pow_one, show ψ a = 0 from ha, map_zero, zero_mul]
        · obtain ⟨n, a, ha⟩ := loc j
          refine ⟨n, a, ?_⟩
          change ψ a = ψ (lam j ^ n) * x₀
          rw [map_pow, ha])
    exact this
  choose r hr using fun l => exists_isRatio (t l) t₀
  exact ⟨(main r hr).1, fun r hr => (main r hr).2⟩

theorem iSup_nonzeroLocus_of_inSpan {f : X ⟶ Y} {H : LB X} {ι κ : Type} [Fintype ι]
    {s : κ → LB.Sec H} (hcov : ⨆ j, nonzeroLocus (s j) = ⊤) {t : ι → LB.Sec H}
    (hst : ∀ j, InSpan f t (s j)) : ⨆ l, nonzeroLocus (t l) = ⊤ := by
  refine top_le_iff.1 fun x _ => ?_
  obtain ⟨j, hj⟩ := Opens.mem_iSup.1 (show x ∈ ⨆ j, nonzeroLocus (s j) by rw [hcov]; trivial)
  obtain ⟨k, hk⟩ := exists_chart_of_mem _ hj
  obtain ⟨c, hc⟩ := hst j
  have u := (mem_nonzeroLocus_iff_gs (s j) (𝟙 X) x hk).1 hj
  rw [hc, gs_sum' (𝟙 X) x _ hk] at u
  obtain ⟨l, -, hl⟩ := IsLocalRing.exists_of_isUnit_sum u
  rw [gs_mul (𝟙 X) x _ hk] at hl
  exact Opens.mem_iSup.2
    ⟨l, (mem_nonzeroLocus_iff_gs (t l) (𝟙 X) x hk).2 (isUnit_of_mul_isUnit_right hl)⟩

theorem EmbedsBy.of_inSpan {f : X ⟶ Y} [IsAffine Y] [UniversallyClosed f] {H : LB X}
    {ι κ : Type} [Fintype ι] [Finite κ] {s : κ → LB.Sec H} (hs : EmbedsBy f s) {t : ι → LB.Sec H}
    (hst : ∀ j, InSpan f t (s j)) : EmbedsBy f t := by
  refine ⟨iSup_nonzeroLocus_of_inSpan hs.1 hst, fun i => ?_⟩
  obtain ⟨h₁, h₂⟩ := hs.affine_and_surjective hst (t i)
  choose r hr using fun l => exists_isRatio (t l) (t i)
  exact ⟨h₁, r, hr, h₂ r hr⟩

theorem embedsBy_spec_iff {R : Type} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R)) {H : LB X}
    {ι : Type} (s : ι → LB.Sec H) : EmbedsBy f s ↔
      (⨆ i, nonzeroLocus (s i) = ⊤) ∧ ∀ i, IsAffineOpen (nonzeroLocus (s i)) ∧
        ∃ r : ι → Γ(X, nonzeroLocus (s i)), (∀ j, IsRatio (s j) (s i) (r j)) ∧
          Function.Surjective (MvPolynomial.eval₂Hom ((resG X le_top).comp (f.appTop.hom.comp
            (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)) r) := by
  refine and_congr_right fun _ => forall_congr' fun i => and_congr_right fun _ =>
    exists_congr fun r => and_congr_right fun _ => ?_
  have e : MvPolynomial.eval₂Hom ((resG X le_top).comp (f.appTop.hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)) r =
      (MvPolynomial.eval₂Hom (f.appLE ⊤ (nonzeroLocus (s i)) le_top).hom r).comp
        (MvPolynomial.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) :=
    RingHom.ext fun p => (MvPolynomial.eval₂Hom_map_hom
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r
      (f.appLE ⊤ (nonzeroLocus (s i)) le_top).hom p).symm
  rw [e, RingHom.coe_comp]
  exact (Function.Surjective.of_comp_iff _ (MvPolynomial.map_surjective _
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).2)).symm

theorem EmbedsBy.pull {f : X ⟶ Y} {f' : X' ⟶ Y'} {ψ : X' ⟶ X} {g : Y' ⟶ Y} [IsAffine Y]
    [IsAffine Y'] (sq : IsPullback ψ f' f g) {H : LB X} {H' : LB X'} {ι : Type}
    {s : ι → LB.Sec H} (hs : EmbedsBy f s) {s' : ι → LB.Sec H'}
    (hs' : ∀ y : X', ∃ j k, ψ y ∈ H.U j ∧ y ∈ H'.U k ∧ ∃ u : (X'.presheaf.stalk y)ˣ,
      ∀ i, gs ψ y _ ((s i).f j) = u * gs (𝟙 X') y _ ((s' i).f k)) : EmbedsBy f' s' := by
  have : IsAffineHom ψ := MorphismProperty.of_isPullback (P := @IsAffineHom) sq.flip inferInstance
  have loc : ∀ i, nonzeroLocus (s' i) = ψ ⁻¹ᵁ nonzeroLocus (s i) := fun i => by
    ext y
    obtain ⟨j, k, hj, hk, u, e⟩ := hs' y
    refine (mem_nonzeroLocus_iff_gs (s' i) (𝟙 X') y hk).trans
      (Iff.trans ?_ (mem_nonzeroLocus_iff_gs (s i) ψ y hj).symm)
    rw [e, Units.isUnit_units_mul]
  obtain ⟨hcov, hs⟩ := hs
  refine ⟨top_le_iff.1 fun y _ => ?_, fun i => ?_⟩
  · obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (show ψ y ∈ ⨆ i, nonzeroLocus (s i) by rw [hcov]; trivial)
    exact Opens.mem_iSup.2 ⟨i, by rw [loc]; exact hi⟩
  obtain ⟨haff, r, hr, hsurj⟩ := hs i
  refine ⟨by rw [loc]; exact haff.preimage ψ, fun j => (ψ.appLE _ _ (loc i).le).hom (r j),
    fun j => isRatio_of_gs fun y hy => ?_, ?_⟩
  · obtain ⟨l, k, hl, hk, u, e⟩ := hs' y
    refine ⟨k, hk, u.mul_right_inj.1 ?_⟩
    rw [← e, mul_left_comm, ← e, gs_appLE ψ _ _ _ (𝟙 _) y hy, Category.id_comp]
    exact (hr j).gs ψ y ((loc i).le hy) hl
  · have po := (isIso_pushoutSection_iff sq (US := ⊤) (UT := ⊤) (UX := nonzeroLocus (s i)) le_top
      le_top (UY := nonzeroLocus (s' i)) (by rw [loc]; simp)).1
      (isIso_pushoutSection_of_isAffineOpen sq _ _ _ (isAffineOpen_top _) (isAffineOpen_top _) haff)
    rw [← RingHom.range_eq_top, ← top_le_iff,
      ← CommRingCat.closure_range_union_range_eq_top_of_isPushout po, Subring.closure_le]
    rintro _ (⟨d, rfl⟩ | ⟨c, rfl⟩)
    · obtain ⟨p, rfl⟩ := hsurj d
      refine ⟨MvPolynomial.map (g.appLE ⊤ ⊤ le_top).hom p, ?_⟩
      rw [MvPolynomial.eval₂Hom_map_hom]
      exact ((congrArg (fun q => MvPolynomial.eval₂Hom q _ p)
        (congrArg CommRingCat.Hom.hom po.w.symm)).trans (MvPolynomial.map_eval₂Hom _ _ _ p).symm)
    · exact ⟨MvPolynomial.C c, MvPolynomial.eval₂Hom_C _ _ _⟩

section Translate

variable {L : LB X} {K K' : Type} [Fintype K] [Fintype K'] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
  {φ' : K' → (Y' ⟶ X)} {ε' : K' → ℤ} {h : Y' ⟶ Y}

theorem secScal_iff_sval (hL : L.IsLB) {s' : LB.Sec (LB.LinComb L φ' ε')}
    {s : LB.Sec (LB.LinComb L φ ε)} : GeneratorPullback.SecScal L φ' ε' s' φ ε s h 1 ↔
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J), Good L z J → sval s (r ≫ h) z J = sval s' r z J :=
  ⟨fun H _ r z _ hJ => SectionScalarValuation.secScal_sval H r z hJ,
    fun H => SectionScalarValuation.secScal_of_sval hL fun y J hJ => H _ _ y J hJ⟩

theorem existsUnique_secScal (hL : L.IsLB) (e : FormEq (fun k => h ≫ φ k) ε φ' ε')
    (s : LB.Sec (LB.LinComb L φ ε)) :
    ∃! s' : LB.Sec (LB.LinComb L φ' ε'), GeneratorPullback.SecScal L φ' ε' s' φ ε s h 1 := by
  obtain ⟨s', hs'⟩ := exists_sec hL e (pullSec L φ ε s h)
  have H : GeneratorPullback.SecScal L φ' ε' s' φ ε s h 1 := (secScal_iff_sval hL).2 fun Z r z J hJ =>
    ((hs' Z r z J hJ).trans (SectionScalarValuation.sval_pullSec φ ε s h r z hJ)).symm
  refine ⟨s', H, fun s'' H' => ?_⟩
  have := funext (sec_ext_val hL (s := s'') (s' := s') fun y J hJ =>
    (SectionScalarValuation.secScal_sval H' _ y hJ).symm.trans (SectionScalarValuation.secScal_sval H _ y hJ))
  cases s'; cases s''; cases this; rfl

theorem secScal_symm (hL : L.IsLB) {s' : LB.Sec (LB.LinComb L φ' ε')}
    {s : LB.Sec (LB.LinComb L φ ε)} (H : GeneratorPullback.SecScal L φ' ε' s' φ ε s h 1) {h' : Y ⟶ Y'}
    (e : h' ≫ h = 𝟙 Y) : GeneratorPullback.SecScal L φ ε s φ' ε' s' h' 1 :=
  (secScal_iff_sval hL).2 fun _ r z _ hJ => by
    rw [← SectionScalarValuation.secScal_sval H (r ≫ h') z hJ, Category.assoc, e, Category.comp_id]

theorem formEq_comp {φ₁ : K' → (Y ⟶ X)} (e : FormEq φ ε φ₁ ε') (h : Y' ⟶ Y) :
    FormEq (fun k => h ≫ φ k) ε (fun k => h ≫ φ₁ k) ε' := fun U _ v => e U (fun q => v (h ≫ q))

theorem exists_equiv_secScal (hL : L.IsLB) [IsIso h] (e : FormEq (fun k => h ≫ φ k) ε φ' ε') :
    ∃ E : LB.Sec (LB.LinComb L φ ε) ≃ LB.Sec (LB.LinComb L φ' ε'),
      ∀ s s', GeneratorPullback.SecScal L φ' ε' s' φ ε s h 1 ↔ E s = s' := by
  have e' : FormEq (fun k => inv h ≫ φ' k) ε' φ ε := fun U _ v => by
    have := formEq_comp e (inv h) U v
    simp only [IsIso.inv_hom_id_assoc] at this
    exact this.symm
  choose F hF uF using existsUnique_secScal hL e
  choose G hG uG using existsUnique_secScal hL e'
  refine ⟨⟨F, G, fun s => (uG _ _ (secScal_symm hL (hF s) (IsIso.inv_hom_id h))).symm,
    fun s => (uF _ _ (secScal_symm hL (hG s) (IsIso.hom_inv_id h))).symm⟩,
    fun s s' => ⟨fun H => (uF s s' H).symm, ?_⟩⟩
  rintro rfl
  exact hF s

theorem InSpan.secScal (hL : L.IsLB) {B B' : Scheme.{0}} {f : Y ⟶ B} {f' : Y' ⟶ B'} {g : B' ⟶ B}
    (w : h ≫ f = f' ≫ g) {ι : Type} [Fintype ι] {t : ι → LB.Sec (LB.LinComb L φ ε)}
    {s : LB.Sec (LB.LinComb L φ ε)} (hs : InSpan f t s) {t' : ι → LB.Sec (LB.LinComb L φ' ε')}
    {s' : LB.Sec (LB.LinComb L φ' ε')} (ht' : ∀ l, GeneratorPullback.SecScal L φ' ε' (t' l) φ ε (t l) h 1)
    (hs' : GeneratorPullback.SecScal L φ' ε' s' φ ε s h 1) : InSpan f' t' s' := by
  obtain ⟨c, hc⟩ := hs
  refine ⟨fun l => g.appTop.hom (c l), fun j => fn_ext fun y hy => ?_⟩
  choose I hI using fun χ : Y' ⟶ X => exists_chart hL (χ y)
  have hI' : Good L y I := hI
  have hm := hI'.mem φ (𝟙 Y' ≫ h)
  refine (sec_trans s' (𝟙 Y') y hy (hI'.mem φ' (𝟙 Y'))).trans ?_
  change _ * sval s' (𝟙 Y') y I = _
  rw [← SectionScalarValuation.secScal_sval hs' _ y hI', sval]
  refine (congrArg _ ((congrArg (gs _ y _) (hc _)).trans (gs_sum' _ y _ hm _))).trans (Eq.trans ?_ (gs_sum' (𝟙 Y') y _ hy _).symm)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  refine (congrArg _ (gs_mul _ y _ hm _ _)).trans (Eq.trans ?_ (gs_mul (𝟙 Y') y _ hy _ _).symm)
  refine (mul_left_comm _ _ _).trans (congrArg₂ (· * ·) ?_ ?_)
  · refine (gs_const f _ _ y hm _).trans (Eq.trans ?_ (gs_const f' _ (𝟙 Y') y hy _).symm)
    rw [Category.assoc, w, ← Category.assoc]
    exact (gs_pull _ g y ⊤ trivial _).symm
  · refine Eq.trans ?_ (sec_trans (t' l) (𝟙 Y') y hy (hI'.mem φ' (𝟙 Y'))).symm
    exact congrArg _ (SectionScalarValuation.secScal_sval (ht' l) _ y hI')

theorem EmbedsBy.secScal (hL : L.IsLB) {B B' : Scheme.{0}} [IsAffine B] [IsAffine B'] {f : Y ⟶ B}
    {f' : Y' ⟶ B'} {g : B' ⟶ B} (sq : IsPullback h f' f g) {ι : Type}
    {s : ι → LB.Sec (LB.LinComb L φ ε)} (hs : EmbedsBy f s) {s' : ι → LB.Sec (LB.LinComb L φ' ε')}
    (hs' : ∀ i, GeneratorPullback.SecScal L φ' ε' (s' i) φ ε (s i) h 1) : EmbedsBy f' s' := by
  refine hs.pull sq fun y => ?_
  choose I hI using fun χ : Y' ⟶ X => exists_chart hL (χ y)
  have hI' : Good L y I := hI
  refine ⟨_, _, hI'.mem φ h, hI'.mem φ' (𝟙 Y'), 1, fun i => ?_⟩
  have := SectionScalarValuation.secScal_sval (hs' i) (𝟙 Y') y hI'
  rw [Category.id_comp] at this
  rw [Units.val_one, one_mul]
  exact this

theorem formEq_const {χ χ' : Y ⟶ X} (e : χ = χ') (hε : ∑ k, ε k = ∑ k, ε' k) :
    FormEq (fun _ : K => χ) ε (fun _ : K' => χ') ε' := fun U _ v => by
  have key : ∀ (K : Type) [Fintype K] (ε : K → ℤ) (a : U), ∏ k, a ^ ε k = a ^ ∑ k, ε k :=
    fun K _ ε a => (map_prod (zpowersHom U a) (fun k => Multiplicative.ofAdd (ε k)) _).symm
  rw [e]
  exact (key K ε _).trans ((congrArg _ hε).trans (key K' ε' _).symm)

theorem secScal_const_iff (hL : L.IsLB) {χ : Y ⟶ X} {χ' : Y' ⟶ X} (e : h ≫ χ = χ')
    {s' : LB.Sec (LB.LinComb L (fun _ : K' => χ') ε')} {s : LB.Sec (LB.LinComb L (fun _ : K => χ) ε)} :
    GeneratorPullback.SecScal L (fun _ => χ') ε' s' (fun _ => χ) ε s h 1 ↔
      ∀ (i : L.ι) (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z), χ' (r z) ∈ L.U i →
        gs (r ≫ h) z _ (s.f fun _ => i) = gs r z _ (s'.f fun _ => i) := by
  subst e
  rw [secScal_iff_sval hL]
  refine ⟨fun H i Z r z hz => ?_, fun H Z r z J hJ => ?_⟩
  · obtain ⟨J, hJ, e⟩ := exists_good L hL z (K := PUnit) (fun _ => r ≫ h ≫ χ) (fun _ => i)
      (fun _ _ _ => rfl) (fun _ => hz)
    have := H Z r z J hJ
    rwa [sval_of s (r ≫ h) z J (fun _ => i) (fun _ => by rw [Category.assoc]; exact e ⟨⟩),
      sval_of s' r z J (fun _ => i) (fun _ => e ⟨⟩)] at this
  · rw [sval_of s (r ≫ h) z J (fun _ => J (r ≫ h ≫ χ)) (fun _ => by rw [Category.assoc])]
    exact H _ Z r z (hJ (r ≫ h ≫ χ))

end Translate

section Group

variable {S : Scheme.{0}} (A : Over S) [GrpObj A] {L : LB A.left} {N : ℕ}

omit [GrpObj A] in

theorem exists_isPullback_restrict {U : S.Opens} {φ : X' ⟶ A.left} {f' : X' ⟶ Y'}
    {g : Y' ⟶ U.toScheme} (sq : IsPullback φ f' A.hom (g ≫ U.ι)) :
    ∃ h : X' ⟶ (A.hom ⁻¹ᵁ U).toScheme, h ≫ (A.hom ⁻¹ᵁ U).ι = φ ∧
      IsPullback h f' (A.hom ∣_ U) g := by
  have P := (isPullback_morphismRestrict A.hom U).flip
  refine ⟨P.lift φ (f' ≫ g) (sq.w.trans (Category.assoc _ _ _).symm), P.lift_fst _ _ _, ?_⟩
  refine IsPullback.of_right ?_ (P.lift_snd _ _ _) P
  rw [P.lift_fst]
  exact sq

theorem sum_one_fin (N : ℕ) : ∑ _ : Fin N, (1 : ℤ) = ∑ _ : Fin 1, (N : ℤ) := by simp

theorem embedsBy_powOver_of_inSpan [UniversallyClosed A.hom] {U : S.Opens} (hU : IsAffineOpen U)
    {M : ℕ} {s : Fin (M + 1) → LB.Sec (powOver A L U N)} (hs : EmbedsBy (A.hom ∣_ U) s)
    {ι : Type} [Fintype ι] (t : ι → LB.Sec (powOver A L U N))
    (hst : ∀ j, InSpan (A.hom ∣_ U) t (s j)) : EmbedsBy (A.hom ∣_ U) t :=
  have : IsAffine U := hU
  hs.of_inSpan hst

theorem embedsBy_powOver [UniversallyClosed A.hom] (hA : VeryAmpleAt A L N) {U : S.Opens}
    (hU : IsAffineOpen U) {ι : Type} [Fintype ι] (t : ι → LB.Sec (powOver A L U N))
    (ht : ∀ s, InSpan (A.hom ∣_ U) t s) : EmbedsBy (A.hom ∣_ U) t := by
  obtain ⟨M, s, hs⟩ := (veryAmpleAt_iff A L N).1 hA U hU
  exact embedsBy_powOver_of_inSpan A hU hs t fun j => ht _

theorem exists_embedsBy_of_isPullback (hL : L.IsLB) (hA : VeryAmpleAt A L N) {U : S.Opens}
    (hU : IsAffineOpen U) [IsAffine Y'] {φ : X' ⟶ A.left} {f' : X' ⟶ Y'} {g : Y' ⟶ U.toScheme}
    (sq : IsPullback φ f' A.hom (g ≫ U.ι)) {K : Type} [Fintype K] {ε : K → ℤ}
    (hε : ∑ k, ε k = N) :
    ∃ M : ℕ, ∃ s : Fin (M + 1) → LB.Sec (LB.LinComb L (fun _ : K => φ) ε), EmbedsBy f' s := by
  have : IsAffine U := hU
  obtain ⟨M, s, hs⟩ := (veryAmpleAt_iff A L N).1 hA U hU
  obtain ⟨h, e, sq'⟩ := exists_isPullback_restrict A sq
  choose s' hs' _ using fun i => existsUnique_secScal hL (φ := fun _ : Fin N => (A.hom ⁻¹ᵁ U).ι)
    (ε := fun _ => 1) (h := h) (formEq_const (K' := K) (ε' := ε) e (by simp [hε])) (s i)
  exact ⟨M, s', EmbedsBy.secScal hL sq' hs hs'⟩

theorem embedsBy_of_isPullback [UniversallyClosed A.hom] (hL : L.IsLB) (hA : VeryAmpleAt A L N)
    {U : S.Opens} (hU : IsAffineOpen U) [IsAffine Y'] {φ : X' ⟶ A.left} {f' : X' ⟶ Y'}
    {g : Y' ⟶ U.toScheme} (sq : IsPullback φ f' A.hom (g ≫ U.ι)) {K : Type} [Fintype K]
    {ε : K → ℤ} (hε : ∑ k, ε k = N) {ι : Type} [Fintype ι]
    (t : ι → LB.Sec (LB.LinComb L (fun _ : K => φ) ε)) (ht : ∀ s, InSpan f' t s) :
    EmbedsBy f' t ∧ ∀ t₀ : LB.Sec (LB.LinComb L (fun _ : K => φ) ε),
      IsAffineOpen (nonzeroLocus t₀) ∧ ∀ r : ι → Γ(X', nonzeroLocus t₀),
        (∀ l, IsRatio (t l) t₀ (r l)) → Function.Surjective
          (MvPolynomial.eval₂Hom (f'.appLE ⊤ (nonzeroLocus t₀) le_top).hom r) := by
  have : UniversallyClosed f' :=
    MorphismProperty.of_isPullback (P := @UniversallyClosed) sq inferInstance
  obtain ⟨M, s, hs⟩ := exists_embedsBy_of_isPullback A hL hA hU sq hε
  exact ⟨hs.of_inSpan fun j => ht _, hs.affine_and_surjective fun j => ht _⟩

omit [GrpObj A] in
theorem comp_topIso_inv_ι (g : Y' ⟶ S) : (g ≫ S.topIso.inv) ≫ (⊤ : S.Opens).ι = g := by simp

theorem embeds_by_global_sections [IsAffine S] [UniversallyClosed A.hom] (hL : L.IsLB) (hA : VeryAmpleAt A L N)
    {ι : Type} [Fintype ι] (t : ι → H0 L N) (ht : ∀ s, InSpan A.hom t s) : EmbedsBy A.hom t :=
  (embedsBy_of_isPullback A hL hA (isAffineOpen_top S) (g := 𝟙 S ≫ S.topIso.inv)
    (by rw [comp_topIso_inv_ι]; exact IsPullback.of_id_fst) (by simp) t ht).1

theorem inSpan_iff_mem_span {a : ℤ} {T : Over S} {ι : Type} [Fintype ι]
    (t : ι → LB.Sec (LPow A L a T)) (s : LB.Sec (LPow A L a T)) :
    InSpan (fst T A).left t s ↔ SecM.ofSec A s ∈
      Submodule.span Γ(T.left, ⊤) (Set.range fun i => (SecM.ofSec A (t i) : SecM A L a T)) := by
  rw [Submodule.mem_span_range_iff_exists_fun]
  refine exists_congr fun c => ?_
  rw [Subtype.ext_iff, Submodule.coe_sum, eq_comm, funext_iff]
  refine forall_congr' fun k => ?_
  rw [Finset.sum_apply]
  rfl

theorem embedsBy_LPow [UniversallyClosed A.hom] (hL : L.IsLB) (hA : VeryAmpleAt A L N)
    {U : S.Opens} (hU : IsAffineOpen U) (T : Over S) [IsAffine T.left] (g : T.left ⟶ U.toScheme)
    (hg : g ≫ U.ι = T.hom) {ι : Type} [Fintype ι] (t : ι → LB.Sec (LPow A L N T))
    (ht : Submodule.span Γ(T.left, ⊤)
      (Set.range fun i => (SecM.ofSec A (t i) : SecM A L N T)) = ⊤) :
    EmbedsBy (fst T A).left t :=
  (embedsBy_of_isPullback A hL hA hU (g := g) (φ := (snd T A).left)
    (by rw [hg]; exact (IsPullback.of_hasPullback T.hom A.hom).flip) (by simp) t
    fun s => (inSpan_iff_mem_span A t s).2 (by rw [ht]; trivial)).1

theorem embedsBy_baseAt [UniversallyClosed A.hom] (hL : L.IsLB) (hA : VeryAmpleAt A L N)
    {V : S.Opens} (hV : IsAffineOpen V) {R : Type} [CommRing R]
    (x : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver S) V).left) {ι : Type} [Fintype ι]
    (t : ι → LB.Sec (LPow A L N (baseAt x)))
    (ht : Submodule.span Γ((baseAt x).left, ⊤)
      (Set.range fun i => (SecM.ofSec A (t i) : SecM A L N (baseAt x))) = ⊤) :
    EmbedsBy (fst (baseAt x) A).left t :=
  have : IsAffine (baseAt x).left := inferInstanceAs (IsAffine (Spec (CommRingCat.of R)))
  embedsBy_LPow A hL hA hV (baseAt x) x (congrArg (x ≫ ·) (Category.comp_id V.ι).symm) t ht

theorem translate_powOver_LPow (hL : L.IsLB) (N : ℕ) {U : S.Opens} (T : Over S)
    (g : T.left ⟶ U.toScheme) (hg : g ≫ U.ι = T.hom) :
    ∃ h : (T ⊗ A).left ⟶ (A.hom ⁻¹ᵁ U).toScheme, h ≫ (A.hom ⁻¹ᵁ U).ι = (snd T A).left ∧
      IsPullback h (fst T A).left (A.hom ∣_ U) g ∧
      (∀ s : LB.Sec (powOver A L U N), ∃! s' : LB.Sec (LPow A L N T),
        GeneratorPullback.SecScal L _ _ s' _ _ s h 1) ∧
      (IsIso g → ∃ E : LB.Sec (powOver A L U N) ≃ LB.Sec (LPow A L N T),
        ∀ s s', GeneratorPullback.SecScal L _ _ s' _ _ s h 1 ↔ E s = s') := by
  obtain ⟨h, e, sq⟩ := exists_isPullback_restrict A (φ := (snd T A).left) (f' := (fst T A).left)
    (g := g) (by rw [hg]; exact (IsPullback.of_hasPullback T.hom A.hom).flip)
  refine ⟨h, e, sq, fun s => existsUnique_secScal hL (formEq_const e (sum_one_fin N)) s, fun _ => ?_⟩
  have : IsIso h := sq.isIso_fst_of_isIso
  exact exists_equiv_secScal hL (formEq_const e (sum_one_fin N))

omit [GrpObj A] in

theorem global_sections_power_over_top (hL : L.IsLB) (N : ℕ) :
    ∃ E : H0 L N ≃ LB.Sec (powOver A L ⊤ N),
      ∀ s s', GeneratorPullback.SecScal L _ _ s' _ _ s (A.hom ⁻¹ᵁ ⊤).ι 1 ↔ E s = s' :=
  have : IsIso (A.hom ⁻¹ᵁ ⊤).ι := A.left.topIso.isIso_hom
  exists_equiv_secScal hL (formEq_const (Category.comp_id _) (sum_one_fin N).symm)

end Group

theorem polarized_abelian_embeds_by_sections (hA : AmpleSt) {S : Scheme.{0}} [IsAffine S] [IsLocallyNoetherian S]
    (P : PolAV S) {N : ℕ} (hN : 4 ≤ N) {ι : Type} [Fintype ι] (t : ι → H0 P.L N)
    (ht : ∀ s, InSpan P.A.hom t s) : EmbedsBy P.A.hom t :=
  have := P.isAb.proper
  embeds_by_global_sections P.A P.isLB (hA S P N hN).2 t ht

theorem exists_embedsBy_polAV {S : Scheme.{0}} (P : PolAV S) {U : S.Opens} (hU : IsAffineOpen U) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ M : ℕ, ∃ s : Fin (M + 1) → LB.Sec (powOver P.A P.L U N),
      EmbedsBy (P.A.hom ∣_ U) s := P.ample U hU

end GlobalTheory.AmpleSpan
