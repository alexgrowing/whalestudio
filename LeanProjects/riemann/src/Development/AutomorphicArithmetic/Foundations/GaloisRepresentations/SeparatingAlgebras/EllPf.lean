import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StGlob
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantZmodLift
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.ell_pf :
    UpperTheory.Gal.Gen.EllGrp → UpperTheory.Gal.Gen.Ell := by
  intro hGrp E _ _ _ n C hLev H _ lam hU2 hfin
  have hC := hLev.fin
  have hCc := hLev.compact
  obtain ⟨U1, hU1o, hU11, hU1C⟩ := hLev.isOpen
  obtain ⟨U2, hU2o, hU21, hU2l⟩ := hU2
  set D : Subgroup (UA E n) := C ⊔ infU E n with hDdef
  have hDC : D ≤ C.comap GlobalTheory.EllU.finPart := sup_le (fun c hc => by
      change GlobalTheory.EllU.finPart c ∈ C
      rw [GlobalTheory.EllU.finPart_of_finU (hC hc)]; exact hc)
    (fun x hx => by
      change GlobalTheory.EllU.finPart x ∈ C
      rw [GlobalTheory.EllU.finPart_of_infU hx]; exact C.one_mem)
  let f : D →* C := (GlobalTheory.EllU.finPart.comp D.subtype).codRestrict C (fun d => hDC d.2)
  let lam' : D →* H := lam.comp f
  haveI := GlobalTheory.InfUCompact.compactSpace_infU E n
  have hI : IsCompact (infU E n : Set (UA E n)) := isCompact_iff_compactSpace.2 inferInstance
  have hDc : IsCompact (D : Set (UA E n)) := by
    rw [hDdef, Subgroup.mul_normal]
    exact hCc.mul hI
  have hyp : ∀ g : UA E n, ∀ γ ∈ ratU E n, ∀ d : D, γ * g = g * d → lam' d = 1 := by
    intro g γ hγ d h
    have hγ' : g * (d : UA E n) * g⁻¹ ∈ ratU E n := by
      rw [← h, mul_inv_cancel_right]; exact hγ
    have hd : IsOfFinOrder (d : UA E n) := GlobalTheory.T.isOfFinOrder_of_compact_conj_mem_unitaryRationalPoints E n D hDc g d d.2 hγ'
    obtain ⟨m, hm, hpow⟩ := isOfFinOrder_iff_pow_eq_one.1 hd
    have hdm : d ^ m = 1 := Subtype.ext (by rw [Subgroup.coe_pow, hpow]; rfl)
    exact hfin (f d) (isOfFinOrder_iff_pow_eq_one.2 ⟨m, hm, by rw [← map_pow, hdm, map_one]⟩)
  obtain ⟨ℓ, h1, h2⟩ := hGrp (UA E n) H (ratU E n) D lam' hyp
  have hinf : ∀ g, ∀ x ∈ infU E n, ℓ (g * x) = ℓ g := by
    intro g x hx
    have e : f ⟨x, le_sup_right (a := C) hx⟩ = 1 := Subtype.ext (GlobalTheory.EllU.finPart_of_infU hx)
    have := h2 g ⟨x, le_sup_right (a := C) hx⟩
    simp only [lam', MonoidHom.comp_apply, e, map_one, mul_one] at this
    exact this
  have hC' : ∀ g (c : C), ℓ (g * c) = ℓ g * lam c := by
    intro g c
    have e : f ⟨c, le_sup_left (b := infU E n) c.2⟩ = c := Subtype.ext (GlobalTheory.EllU.finPart_of_finU (hC c.2))
    have := h2 g ⟨c, le_sup_left (b := infU E n) c.2⟩
    simp only [lam', MonoidHom.comp_apply, e] at this
    exact this
  set Wn : Set (UA E n) := GlobalTheory.EllU.finPart ⁻¹' (U1 ∩ U2) with hWn
  have hWo : IsOpen Wn := (hU1o.inter hU2o).preimage GlobalTheory.EllU.continuous_finPart
  have hW1 : (1 : UA E n) ∈ Wn := by
    change GlobalTheory.EllU.finPart 1 ∈ U1 ∩ U2
    rw [map_one]; exact ⟨hU11, hU21⟩
  have hWinv : ∀ g, ∀ w ∈ Wn, ℓ (g * w) = ℓ g := by
    intro g w hw
    obtain ⟨hw1, hw2⟩ := hw
    have hkC : GlobalTheory.EllU.finPart w ∈ C := hU1C ⟨hw1, GlobalTheory.EllU.finPart_mem w⟩
    have hl : lam ⟨GlobalTheory.EllU.finPart w, hkC⟩ = 1 := hU2l ⟨GlobalTheory.EllU.finPart w, hkC⟩ hw2
    have e : g * w = g * GlobalTheory.EllU.finPart w * ((GlobalTheory.EllU.finPart w)⁻¹ * w) := by group
    rw [e, hinf _ _ (GlobalTheory.EllU.inv_finPart_mul_mem w)]
    have := hC' g ⟨GlobalTheory.EllU.finPart w, hkC⟩
    rw [hl, mul_one] at this
    exact this
  refine ⟨ℓ, hinf, hC', fun φ => ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine continuous_iff_continuousAt.2 fun g => ?_
    refine (continuousAt_const (y := φ (ℓ g))).congr ?_
    have hc : Continuous fun y : UA E n => g⁻¹ * y := continuous_const.mul continuous_id
    have hm : Wn ∈ nhds (g⁻¹ * g) := by
      rw [inv_mul_cancel]; exact hWo.mem_nhds hW1
    filter_upwards [hc.continuousAt.preimage_mem_nhds hm] with y hy
    change φ (ℓ g) = φ (ℓ y)
    have := hWinv g _ hy
    rw [mul_inv_cancel_left] at this
    rw [this]
  · intro γ hγ g
    change φ (ℓ (γ * g)) = φ (ℓ g)
    rw [h1 γ hγ g]
  · let S : Subgroup (finU E n) :=
      { carrier := {k | RU E n k (fun g => φ (ℓ g)) = fun g => φ (ℓ g)}
        one_mem' := by
          change RU E n 1 _ = _
          rw [map_one]; rfl
        mul_mem' := fun {a b} ha hb => by
          change RU E n ((a : UA E n) * b) _ = _
          rw [map_mul, Module.End.mul_apply]
          change RU E n a (RU E n b _) = _
          rw [hb, ha]
        inv_mem' := fun {a} ha => by
          change RU E n ((a : UA E n)⁻¹) _ = _
          conv_lhs => rw [← ha]
          change RU E n ((a : UA E n)⁻¹) (RU E n a _) = _
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl }
    change IsOpen (S : Set (finU E n))
    refine Subgroup.isOpen_of_mem_nhds S (g := 1) ?_
    have ho : IsOpen ((Subtype.val : finU E n → UA E n) ⁻¹' Wn) := hWo.preimage continuous_subtype_val
    refine Filter.mem_of_superset (ho.mem_nhds hW1) fun k hk => ?_
    change RU E n k _ = _
    funext g
    change φ (ℓ (g * k)) = φ (ℓ g)
    rw [hWinv g _ hk]
  · refine FiniteDimensional.span_of_finite ℂ ((Set.finite_singleton (fun g => φ (ℓ g))).subset ?_)
    rintro _ ⟨k, rfl⟩
    change RU E n k _ = _
    funext g
    change φ (ℓ (g * k)) = φ (ℓ g)
    rw [hinf g k k.2]
