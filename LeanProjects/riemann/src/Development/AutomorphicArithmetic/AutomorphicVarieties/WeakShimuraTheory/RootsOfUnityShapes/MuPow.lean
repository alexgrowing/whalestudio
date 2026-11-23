import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CongrFacts
import GroundTheory.GlobalFields.CyclotomicCharacters.PadicUnitsLog

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem mu_pow {Γ M : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CommGroup M] {l : ℕ}
    (f : Γ →* M) (hf : IsClosed (f.ker : Set Γ)) {H : Subgroup Γ} {s : Γ} (hs : s ∈ muOf l H) :
    ∃ a : ℕ, f s ^ l ^ a = 1 := by
  obtain ⟨-, a, ha⟩ := hs
  refine ⟨a, ?_⟩
  have hle : ⁅H, H⁆ ≤ f.ker := by
    rw [Subgroup.commutator_le]
    intro x _ y _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_commute]
    exact Commute.all _ _
  have hmem := Subgroup.topologicalClosure_minimal _ hle hf ha
  rwa [MonoidHom.mem_ker, map_pow] at hmem

private theorem one_of {M : Type} [Monoid M] {x : M} {l a m : ℕ} (h : l.Coprime m) (h1 : x ^ l ^ a = 1)
    (h2 : x ^ m = 1) : x = 1 := by
  have hc : Nat.Coprime (l ^ a) m := Nat.Coprime.pow_left a h
  have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2)
  rw [Nat.Coprime.gcd_eq_one hc, Nat.dvd_one, orderOf_eq_one_iff] at hd
  exact hd

theorem UpperTheory.V.Ws.Rq.muPs :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ T : Tower D, T.Ok →
      ∀ H : Subgroup (G T.F Ω), ∀ s ∈ muOf l H, ∀ i, D.ps i (resQ T.F s) = 1 := by
  intro Ω _ _ _ l _ c D hD T hT H s hs i
  haveI : IsAlgClosure T.F Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) T.F⟩
  have hcont : Continuous (resQ T.F) := (galEmbTop ℚ T.F Ω).1.continuous
  have hlp : l.Prime := Fact.out
  have gen : ∀ (χ : G ℚ Ω →* (c.O)ˣ) (m : ℕ), l.Coprime m →
      IsClosed ((χ.comp (resQ T.F)).ker : Set (G T.F Ω)) → χ (resQ T.F s) ^ m = 1 → χ (resQ T.F s) = 1 := by
    intro χ m hm hcl h2
    obtain ⟨a, ha⟩ := mu_pow (χ.comp (resQ T.F)) hcl hs
    exact one_of hm ha h2
  have closedOfOpen : ∀ χ : G ℚ Ω →* (c.O)ˣ, IsOpen (χ.ker : Set (G ℚ Ω)) →
      IsClosed ((χ.comp (resQ T.F)).ker : Set (G T.F Ω)) := by
    intro χ ho
    have hc : IsClosed (χ.ker : Set (G ℚ Ω)) := Subgroup.isClosed_of_isOpen _ ho
    rw [← MonoidHom.comap_ker]
    exact hc.preimage hcont
  have hcyc : cycZ T.F Ω l s = 1 := by
    have hcl : IsClosed ((cycZ T.F Ω l).ker : Set (G T.F Ω)) :=
      isClosed_singleton.preimage (continuous_cycZ T.F Ω l)
    obtain ⟨a, ha⟩ := mu_pow (cycZ T.F Ω l) hcl hs
    have htor : cycZ T.F Ω l s ^ GroundTheory.Global.Cyclotomic.torsionExponent l = 1 :=
      (GroundTheory.Global.Cyclotomic.mem_torsion_iff l _).1
        ((CommGroup.mem_torsion _).2 (isOfFinOrder_iff_pow_eq_one.2 ⟨l ^ a, pow_pos hlp.pos a, ha⟩))
    have hcop : l.Coprime (GroundTheory.Global.Cyclotomic.torsionExponent l) := by
      simp only [GroundTheory.Global.Cyclotomic.torsionExponent, hD.l_odd, if_false]
      exact Nat.coprime_of_lt_prime (Nat.sub_pos_of_lt hlp.one_lt).ne' (Nat.sub_lt hlp.pos one_pos) hlp
    exact one_of hcop ha htor
  have hchi : chiO ℚ Ω l c.O (resQ T.F s) = 1 := by
    have e : cycZ ℚ Ω l (resQ T.F s) = cycZ T.F Ω l s := rfl
    simp only [chiO, MonoidHom.comp_apply]
    rw [e, hcyc, map_one]
  obtain ⟨m, hm, hkc⟩ := hT.kc
  have hψ : D.ψ (resQ T.F s) = 1 := gen D.ψ m hm (closedOfOpen _ hD.psi_open) (hkc s hcyc)
  obtain ⟨m', hm', hξm⟩ := hD.xi_ord
  have hξ : D.ξ (resQ T.F s) = 1 :=
    gen D.ξ m' hm' (closedOfOpen _ hD.xi_open) (by rw [← MonoidHom.pow_apply, hξm, MonoidHom.one_apply])
  have hom : D.om (resQ T.F s) = 1 := by
    have hb := hD.om_bar (resQ T.F s)
    have hb' : residue c.O ↑(D.om (resQ T.F s)) = residue c.O ↑(1 : (c.O)ˣ) := by
      have e1 : Raw.bar D.om (resQ T.F s) = residue c.O ↑(D.om (resQ T.F s)) := rfl
      have e2 : Raw.bar (chiO ℚ Ω l c.O) (resQ T.F s) = residue c.O ↑(chiO ℚ Ω l c.O (resQ T.F s)) := rfl
      rw [← e1, hb, e2, hchi]
    apply (congrFacts Ω l c).2.2.2.1 _ 1 (l - 1)
    · exact Nat.not_dvd_of_pos_of_lt (Nat.sub_pos_of_lt hlp.one_lt) (Nat.sub_lt hlp.pos one_pos)
    · rw [← MonoidHom.pow_apply, hD.om_pow, MonoidHom.one_apply]
    · exact one_pow _
    · rw [← residue_eq_zero_iff, map_sub, hb', sub_self]
  have hal : D.al (resQ T.F s) = 1 := by
    simp only [Raw.al, MonoidHom.mul_apply, MonoidHom.inv_apply, hchi, hom, hξ, inv_one, mul_one]
  have hPsi : D.Psi (resQ T.F s) = 1 := by
    simp only [Raw.Psi, UpperTheory.V.Chr.Psi, MonoidHom.mul_apply, MonoidHom.pow_apply, MonoidHom.zpow_apply,
      hψ, hchi, one_pow, one_zpow, mul_one]
  have hth : D.th (resQ T.F s) = 1 := by
    simp only [Raw.th, Raw.al, MonoidHom.mul_apply, MonoidHom.inv_apply, hchi, hom, hξ, hPsi, inv_one, mul_one]
  fin_cases i
  · exact hth
  · exact hPsi
  · exact hal
  · rfl
