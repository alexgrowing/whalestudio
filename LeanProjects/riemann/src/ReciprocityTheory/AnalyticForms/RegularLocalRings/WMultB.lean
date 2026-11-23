import ReciprocityTheory.AnalyticForms.RegularLocalRings.WMultA

namespace ReciprocityTheory.AnForm.R.WMult

open AlgebraicGeometry CategoryTheory MvPolynomial

variable {W : Scheme.{0}} {s : W ⟶ Spec (.of ℂ)}

theorem secHom_surjective (P : AffPres s) : Function.Surjective P.secHom := by
  unfold AffPres.secHom
  rw [RingHom.coe_comp, RingHom.coe_comp, RingHom.coe_comp]
  have i1 : IsIso P.iso.hom.appTop := by
    have : IsIso (Scheme.Γ.map P.iso.hom.op) := inferInstance
    simpa using this
  refine (ConcreteCategory.bijective_of_isIso P.V.topIso.hom).2.comp ?_
  refine (ConcreteCategory.bijective_of_isIso P.iso.hom.appTop).2.comp ?_
  refine (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (.of (MvPolynomial (Fin P.n) ℂ ⧸ P.K))).inv).2.comp ?_
  exact Ideal.Quotient.mk_surjective

theorem isUnit_algebraMap_of_eval_ne_zero {n : ℕ} (K : Ideal (MvPolynomial (Fin n) ℂ))
    (p : Fin n → ℂ) {g : MvPolynomial (Fin n) ℂ} (hg : eval p g ≠ 0) :
    IsUnit (algebraMap _ (locRing K p) g) := by
  have hg' : g ∉ ptIdeal p := fun h => hg (RingHom.mem_ker.mp h)
  have := (IsLocalization.map_units (locPt p) (⟨g, hg'⟩ : (ptIdeal p).primeCompl)).map
    (Ideal.Quotient.mk (Ideal.map (algebraMap (MvPolynomial (Fin n) ℂ) (locPt p)) K))
  rwa [Ideal.Quotient.mk_algebraMap] at this

theorem algebraMap_eq_zero_of_mem {n : ℕ} {K : Ideal (MvPolynomial (Fin n) ℂ)} (p : Fin n → ℂ)
    {k : MvPolynomial (Fin n) ℂ} (hk : k ∈ K) : algebraMap _ (locRing K p) k = 0 := by
  rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_map_of_mem _ hk

theorem map_bd_eq_span {m : ℕ} {I bd : Ideal (MvPolynomial (Fin m) ℂ)} {p : Fin m → ℂ} {e rc : ℕ}
    (S : SncData I bd p e rc) :
    Ideal.map (algebraMap _ (locRing I p)) bd =
      Ideal.span {∏ l ∈ S.J, algebraMap _ (locRing I p) (S.r l)} := by
  obtain ⟨v, hv⟩ := isUnit_algebraMap_of_eval_ne_zero I p S.eval_h
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro g hg
    rw [Ideal.mem_comap]
    have h1 := S.le_span g hg
    have h3 : Ideal.map (algebraMap _ (locRing I p)) (Ideal.span {∏ l ∈ S.J, S.r l} ⊔ I) ≤
        Ideal.span {∏ l ∈ S.J, algebraMap _ (locRing I p) (S.r l)} := by
      rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton, map_prod]
      refine sup_le le_rfl ?_
      rw [Ideal.map_le_iff_le_comap]
      intro k hk
      rw [Ideal.mem_comap, algebraMap_eq_zero_of_mem p hk]
      exact Ideal.zero_mem _
    have h2 := h3 (Ideal.mem_map_of_mem _ h1)
    rw [map_mul] at h2
    have he : algebraMap _ (locRing I p) g =
        ↑v⁻¹ * (algebraMap _ (locRing I p) S.h * algebraMap _ (locRing I p) g) := by
      rw [← hv, ← mul_assoc, Units.inv_mul, one_mul]
    rw [he]
    exact Ideal.mul_mem_left _ _ h2
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    have h1 := Ideal.mem_map_of_mem (algebraMap _ (locRing I p)) S.mem_bd
    rw [map_mul, map_prod] at h1
    have he : ∏ l ∈ S.J, algebraMap _ (locRing I p) (S.r l) =
        ↑v⁻¹ * (algebraMap _ (locRing I p) S.h * ∏ l ∈ S.J, algebraMap _ (locRing I p) (S.r l)) := by
      rw [← hv, ← mul_assoc, Units.inv_mul, one_mul]
    rw [he]
    exact Ideal.mul_mem_left _ _ h1

theorem stalkId_eq_span_of_sncData (P : AffPres s) (Z : W.IdealSheafData) (x : W) (hx : x ∈ P.V)
    (hcl : IsClosed ({x} : Set W)) {e rc : ℕ} (S : SncData P.K (P.bdIdeal Z) (P.coord x hx) e rc) :
    FinalTheorems.stalkId Z x = Ideal.span {∏ l ∈ S.J, W.presheaf.germ P.V x hx (P.secHom (S.r l))} := by
  have hψ : ∀ g, P.stalkEquiv x hx hcl (W.presheaf.germ P.V x hx (P.secHom g)) =
      algebraMap _ (locRing P.K (P.coord x hx)) g :=
    P.stalkEquiv_germ x hx hcl
  have hsecmap : Z.ideal P.affOpen = Ideal.map P.secHom (P.bdIdeal Z) :=
    (Ideal.map_comap_of_surjective _ (secHom_surjective P) _).symm
  have hcompψ : (((P.stalkEquiv x hx hcl : W.presheaf.stalk x →+* locRing P.K (P.coord x hx)).comp
      (W.presheaf.germ P.V x hx).hom).comp P.secHom) =
      algebraMap _ (locRing P.K (P.coord x hx)) :=
    RingHom.ext hψ
  have e1 : Ideal.map (P.stalkEquiv x hx hcl : W.presheaf.stalk x →+* locRing P.K (P.coord x hx))
      (FinalTheorems.stalkId Z x) =
      Ideal.map (P.stalkEquiv x hx hcl : W.presheaf.stalk x →+* locRing P.K (P.coord x hx))
        (Ideal.span {∏ l ∈ S.J, W.presheaf.germ P.V x hx (P.secHom (S.r l))}) := by
    have hZmap : FinalTheorems.stalkId Z x = Ideal.map (W.presheaf.germ P.V x hx).hom
        (Ideal.map P.secHom (P.bdIdeal Z)) := by
      rw [← hsecmap]; exact stalkId_eq_map_germ Z x P.affOpen hx
    rw [hZmap, Ideal.map_map, Ideal.map_map, hcompψ, map_bd_eq_span S,
      Ideal.map_span, Set.image_singleton, map_prod]
    simp only [RingHom.coe_coe, hψ]
  have := congrArg (Ideal.map ((P.stalkEquiv x hx hcl).symm :
    locRing P.K (P.coord x hx) →+* W.presheaf.stalk x)) e1
  rwa [Ideal.map_of_equiv, Ideal.map_of_equiv] at this

theorem rsp_of_sncData (P : AffPres s) (Z : W.IdealSheafData) (x : W) (hx : x ∈ P.V)
    (hcl : IsClosed ({x} : Set W)) {e rc : ℕ} (hdim : ringKrullDim (W.presheaf.stalk x) = e)
    (S : SncData P.K (P.bdIdeal Z) (P.coord x hx) e rc) :
    FinalTheorems.Rsp (W.presheaf.stalk x) e (fun l => W.presheaf.germ P.V x hx (P.secHom (S.r l))) := by
  have hψ : ∀ g, P.stalkEquiv x hx hcl (W.presheaf.germ P.V x hx (P.secHom g)) =
      algebraMap _ (locRing P.K (P.coord x hx)) g :=
    P.stalkEquiv_germ x hx hcl
  rw [P.rsp_iff x hx hcl]
  refine ⟨?_, ?_⟩
  · simp only [hψ]
    exact S.span_eq
  · rw [← P.ringKrullDim_stalk x hx hcl, hdim]

end ReciprocityTheory.AnForm.R.WMult
