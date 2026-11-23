import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.IntUnit
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCmAdeleUnitCharacterReadingHeckeChar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInjectiveCharacterOfIsCyclic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TameHeckeCharTrivialOnFiniteUnitsCongOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdelicCharacterPowEqOneFiniteIdelesOfOrderDvd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharEqOneOfTrivialFinitePartOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNthRootIdeleFinitePartOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdelicCharacterTrivialBaseFiniteIdeles
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFiniteIdeleCharAtDeterminantRoots

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links
  GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TameFinitePart

theorem exists_chrEq_val (D : D7) (χ : HChar D.host.E) (hχ : χ.IsUnitary) :
    ∃ c, ChrEq c χ ∧ ∀ x, ∃ y, ((c x : Circle) : ℂ) = ((χ.1 y : ℂˣ) : ℂ) := by
  obtain ⟨Θ, hc, hinc, hloc⟩ := GlobalTheory.CharTransport.exists_hom D
  let u : (Formalism.L2.Theta.AE D)ˣ →* Neutral.B1.Ideles D.host.E := Units.map Θ.toMonoidHom
  have hu : Continuous u := Continuous.units_map _ hc
  let c' : (Formalism.L2.Theta.AE D)ˣ →* Circle :=
    { toFun := fun x => ⟨((χ.1 (u x) : ℂˣ) : ℂ), mem_sphere_zero_iff_norm.2 (hχ _)⟩
      map_one' := Circle.ext (by simp)
      map_mul' := fun x y => Circle.ext (by
        change ((χ.1 (u (x * y)) : ℂˣ) : ℂ) = ((χ.1 (u x) : ℂˣ) : ℂ) * ((χ.1 (u y) : ℂˣ) : ℂ)
        rw [map_mul, map_mul, Units.val_mul]) }
  have hcoe : ∀ x, ((c' x : Circle) : ℂ) = ((χ.1 (u x) : ℂˣ) : ℂ) := fun x => rfl
  refine ⟨c', ⟨⟨?_, fun x => Circle.ext ?_⟩, fun P e he k x hx => ?_⟩, fun x => ⟨u x, rfl⟩⟩
  · exact Continuous.subtype_mk (Units.continuous_val.comp (χ.2.1.comp hu)) _
  · refine (hcoe _).trans ?_
    have := congrArg (fun y => ((χ.1 y : ℂˣ) : ℂ))
      (Units.ext (hinc x) : u (Units.map (Formalism.L2.Theta.incA D).toMonoidHom x) = Units.map (algebraMap D.host.E _).toMonoidHom x)
    exact this.trans (congrArg (fun y : ℂˣ => (y : ℂ)) (χ.2.2 x))
  · refine (hcoe _).trans (congrArg (fun y => ((χ.1 y : ℂˣ) : ℂ)) (Units.ext ?_))
    change Θ (x : Formalism.L2.Theta.AE D) = _
    rw [hx, hloc P e he]

theorem exists_lift (D : D7) (y : (AfE D)ˣ) : ∃ x : (AE D)ˣ, infPart D (x : AE D) = 1 ∧ finPart D (x : AE D) = y ∧
    finPart D ((x⁻¹ : (AE D)ˣ) : AE D) = ((y⁻¹ : (AfE D)ˣ) : AfE D) := by
  obtain ⟨a, a1, a2⟩ := GlobalTheory.PlaceIdem.parts_surj D 1 (y : AfE D)
  obtain ⟨b, b1, b2⟩ := GlobalTheory.PlaceIdem.parts_surj D 1 ((y⁻¹ : (AfE D)ˣ) : AfE D)
  have h : a * b = 1 := GlobalTheory.PlaceIdem.parts_inj D _ _
    (by rw [RingHom.map_mul, a1, b1, RingHom.map_one, mul_one])
    (by rw [RingHom.map_mul, a2, b2, RingHom.map_one, Units.mul_inv])
  exact ⟨⟨a, b, h, (mul_comm b a).trans h⟩, a1, a2, b2⟩

theorem exists_unit_ne_one {L : Type} [Field L] [NumberField L] (χ : HChar L) (P : HeightOneSpectrum (𝓞 L))
    (ht : χ.TameAt P) (hr : ¬ χ.UnrAt P) : ∃ k : Lˣ, P.valuation L (k : L) = 1 ∧ χ.locK P k ≠ 1 := by
  by_contra hn
  refine hr fun x hx => ?_
  have h1 := (GlobalTheory.Mem.UnitOpen.isOpen_val_le P (-1 : ℤ)).preimage (continuous_sub_left (x : P.adicCompletion L))
  obtain ⟨k, hk⟩ := (HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 L) (K := L) P).exists_mem_open h1 ⟨x, by simp⟩
  have hk' : Valued.v ((x : P.adicCompletion L) - algebraMap L _ k) ≤ WithZero.exp (-1 : ℤ) := hk
  have hx' : Valued.v (x : P.adicCompletion L) = 1 := hx
  have hv : Valued.v (algebraMap L (P.adicCompletion L) k) = 1 := by
    rw [← hx']
    refine (Valuation.map_eq_of_sub_lt _ ?_)
    rw [Valuation.map_sub_swap, hx']
    refine hk'.trans_lt ?_
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  have hv' : P.valuation L k = 1 := (GlobalTheory.BaseIdeleTriv.val_algebraMap P k).symm.trans hv
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at hv'
  have h2 : χ.loc P (atFin P (Units.mk0 k hk0)) = 1 := by
    by_contra h
    exact hn ⟨Units.mk0 k hk0, hv', h⟩
  have e : ((x * (atFin P (Units.mk0 k hk0))⁻¹ : (P.adicCompletion L)ˣ) : P.adicCompletion L) =
      x * (algebraMap L (P.adicCompletion L) k)⁻¹ := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val]; rfl
  have h0 : algebraMap L (P.adicCompletion L) k ≠ 0 := by simpa using hk0
  have h3 := ht (x * (atFin P (Units.mk0 k hk0))⁻¹) (by
    unfold IsUnitAt
    rw [e, map_mul, map_inv₀, hx', hv]; simp) (by
    have : (x : P.adicCompletion L) * (algebraMap L (P.adicCompletion L) k)⁻¹ - 1 =
        ((x : P.adicCompletion L) - algebraMap L _ k) * (algebraMap L (P.adicCompletion L) k)⁻¹ := by
      field_simp
    rw [e, this, map_mul, map_inv₀, hv, inv_one, mul_one]
    simpa using hk')
  rwa [map_mul, map_inv, h2, inv_one, mul_one] at h3

theorem loc_sub_one {E A B : Type} [Field E] [CommRing A] [CommRing B] (i : E →+* A) (f : A →+* B) (e : A) (k : E) (N : ℕ)
    (hN : (N : E) ≠ 0) : f (1 + e * (i k - 1)) - 1 = N • f (e * i ((k - 1) / N)) := by
  rw [← map_nsmul, ← mul_smul_comm, ← map_nsmul, nsmul_eq_mul, mul_div_cancel₀ _ hN, map_add, map_one, map_sub, map_one,
    add_sub_cancel_left]

theorem loc_eq {E A B : Type} [Field E] [CommRing A] [CommRing B] (i : E →+* A) (f : A →+* B) (e : A) (k : E) :
    f (1 + e * (i k - 1)) = 1 + f (e * i (k - 1)) := by
  rw [map_add, map_one, map_sub, map_one]

theorem loc_mul_inv {E A : Type} [Field E] [CommRing A] (i : E →+* A) (e : A) (he : e * e = e) (k : Eˣ) :
    (1 + e * (i k - 1)) * (1 + e * (i ((k⁻¹ : Eˣ) : E) - 1)) = 1 := by
  have hkk : i (k : E) * i ((k⁻¹ : Eˣ) : E) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  linear_combination (i (k : E) - 1) * (i ((k⁻¹ : Eˣ) : E) - 1) * he + e * hkk

set_option maxHeartbeats 800000 in

theorem exists_local (D : D7) (P : HeightOneSpectrum (𝓞 D.host.E)) (k : D.host.Eˣ)
    (hk : P.valuation D.host.E (k : D.host.E) = 1) (N : ℕ) (hN : (N : 𝓞 D.host.E) ∉ P.asIdeal) :
    ∃ (e : AE D) (x : (AE D)ˣ), IsPlIdem D e P ∧ (x : AE D) = locE D e (k : D.host.E) ∧
      IntUnit (Units.map (finPart D).toMonoidHom x) ∧ CongOne N (Units.map (finPart D).toMonoidHom x) := by
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨e, he, -, e1, e2⟩ := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3 P
  have hee : e * e = e := he.1
  have hint : ∀ t : D.host.E, P.valuation D.host.E t ≤ 1 → finPart D (e * incA D t) ∈ intAE D := fun t ht => by
    have h4 : finPart D (incA D t) = (1 : Af D.host.F) ⊗ₜ[D.host.F] t := rfl
    rw [h2, RingHom.map_mul, map_mul, h4, h1]
    intro Q
    rw [GlobalTheory.BaseIdeleTriv.adele_mul_apply]
    by_cases hQ : Q = P
    · subst hQ
      rw [e1, one_mul, GlobalTheory.BaseIdeleTriv.adele_algebraMap_apply, GlobalTheory.BaseIdeleTriv.val_algebraMap]
      exact ht
    · rw [e2 Q hQ, zero_mul, map_zero]
      exact zero_le
  have hone : (1 : AfE D) ∈ intAE D := by
    rw [h2, map_one]
    intro Q
    rw [GlobalTheory.BaseIdeleTriv.adele_one_apply, map_one]
  have hloc : ∀ t : D.host.E, P.valuation D.host.E t = 1 → finPart D (locE D e t) ∈ intAE D := fun t ht => by
    rw [show finPart D (locE D e t) = _ from loc_eq (incA D) (finPart D) e t]
    exact add_mem hone (hint _ (Valuation.map_sub_le _ ht.le (map_one _).le))
  have hm : locE D e (k : D.host.E) * locE D e ((k⁻¹ : D.host.Eˣ) : D.host.E) = 1 := loc_mul_inv (incA D) e hee k
  have hN1 : P.valuation D.host.E (N : D.host.E) = 1 := by
    have := (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := D.host.E) P (r := (N : 𝓞 D.host.E))).2 hN
    simpa using this
  have hN0 : (N : D.host.E) ≠ 0 := by
    intro h
    rw [h, map_zero] at hN1
    exact zero_ne_one hN1
  refine ⟨e, ⟨_, _, hm, (mul_comm _ _).trans hm⟩, he, rfl, ⟨hloc _ hk, hloc _ ?_⟩,
    finPart D (e * incA D (((k : D.host.E) - 1) / N)), hint _ ?_, ?_⟩
  · rw [Units.val_inv_eq_inv_val, map_inv₀, hk, inv_one]
  · rw [map_div₀, hN1, div_one]
    exact Valuation.map_sub_le _ hk.le (map_one _).le
  · exact loc_sub_one (incA D) (finPart D) e k N hN0

set_option maxHeartbeats 1000000 in

theorem exists_xiRec : ∀ (D : D7) (p : ℕ) (δ : Formalism.L2.Host.HChar D.host.E), (p = D.host.pde ∨ p = D.host.pde') → Formalism.L2.Host.IsDelta (H := D.host) p δ → (∀ x, ((δ.1 x : ℂˣ) : ℂ) ∈ FO D) → ∃ (χ : (AE D)ˣ →* Circle) (de : (GlobalTheory.FinalJoin.AfE D)ˣ →* ℂˣ), ChrEq χ δ ∧ XiRec D p de ∧ ∀ (x : (AE D)ˣ) (y : (GlobalTheory.FinalJoin.AfE D)ˣ), Formalism.L2.Theta.finPart D (x : AE D) = (y : GlobalTheory.FinalJoin.AfE D) → ((de y : ℂˣ) : ℂ) = ((χ x : Circle) : ℂ) := by
  intro D p χ hp hδ hval
  obtain ⟨n, hn, ho⟩ := hδ.fin
  obtain ⟨c, h, hcv⟩ := exists_chrEq_val D χ fun x => by
    have h1 : χ.1 x ^ n = 1 := by
      have := DFunLike.congr_fun (congrArg Subtype.val ho) x
      simpa [MonoidHom.pow_apply] using this
    have h2 : ((χ.1 x : ℂˣ) : ℂ) ^ n = 1 := by rw [← Units.val_pow_eq_pow_val, h1, Units.val_one]
    exact Complex.norm_eq_one_of_pow_eq_one h2 hn.ne'
  have h1 : ∀ x, c x ^ n = 1 := GlobalTheory.HeckeFinTrivial.eq_one_of_trivial_on_finite D (c ^ n) ⟨h.1.1.pow n, fun x => by
    rw [MonoidHom.pow_apply, h.1.2, one_pow]⟩ (GlobalTheory.CharOrderFin.char_pow_eq_one_of_orderDvd D c χ h n ho)
  have h2 : ∀ x : (AE D)ˣ, finPart D (x : AE D) = 1 → c x = 1 := fun x hx => by
    obtain ⟨y, rfl⟩ := GlobalTheory.IdeleDiv.exists_pow_eq_of_finPart_eq_one D n hn x hx
    rw [map_pow, h1]
  have h3 : ∀ a, c (idF D a) = 1 := fun a => by
    let b : (AF D.host.F)ˣ := Units.map ((MonoidHom.inr (Ainf D.host.F) (Af D.host.F)).comp
      (MonoidHom.snd (Ainf D.host.F) (Af D.host.F))) a
    let b' : (AF D.host.F)ˣ := Units.map ((MonoidHom.inl (Ainf D.host.F) (Af D.host.F)).comp
      (MonoidHom.fst (Ainf D.host.F) (Af D.host.F))) a
    have e : a = b' * b := Units.ext (Prod.ext (mul_one _).symm (one_mul _).symm)
    rw [e, map_mul, map_mul, h2 (idF D b') rfl, GlobalTheory.BaseIdeleTriv.finite_idele_base_trivial D c χ h hδ.triv b rfl, one_mul]
  obtain ⟨d, hd⟩ := GlobalTheory.DetRootChar.circle_hom_factor (Units.map (finPart D).toMonoidHom) c
    fun x hx => h2 x (congrArg Units.val hx)
  have hd' : ∀ (x : (AE D)ˣ) (y : (AfE D)ˣ), finPart D (x : AE D) = (y : AfE D) → d y = c x := fun x y hxy => by
    rw [← hd x]
    exact congrArg d (Units.ext hxy.symm)
  have hone : ∀ y, d y = 1 → (Circle.toUnits.comp d) y = 1 := fun y hy => by
    rw [MonoidHom.comp_apply, hy, map_one]
  have hcoe : ∀ y, (((Circle.toUnits.comp d) y : ℂˣ) : ℂ) = ((d y : Circle) : ℂ) := fun y => by simp
  have hpp : p.Prime ∧ ∀ i, p ≠ D.host.g i := by
    rcases hp with rfl | rfl
    · exact ⟨D.host.pde_prime, fun i => (D.host.pde_ne_g i).1⟩
    · exact ⟨D.host.pde'_prime, fun i => (D.host.pde_ne_g i).2⟩
  refine ⟨c, Circle.toUnits.comp d, h, ⟨fun y a hy => hone y ?_, fun y a hy => hone y ?_, fun y hy hc => hone y ?_, ?_,
    ⟨n, hn, fun y => ?_⟩, fun y => ?_⟩, fun x y hxy => by rw [hcoe, hd' x y hxy]⟩
  · obtain ⟨x, -, hx, -⟩ := exists_lift D y
    obtain ⟨b, z, hz, hxz⟩ := GlobalTheory.DetRootChar.exists_idF_mul D x (by
      rw [hx, hy]
      change a ⊗ₜ[D.host.F] D.sp.cm.sig 1 = _
      rw [map_one])
    rw [hd' x y hx, hxz, map_mul, h3, h2 z hz, mul_one]
  · have ha : a ≠ 0 := by
      rintro rfl
      obtain ⟨ι, -⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
      obtain ⟨P, -⟩ := GlobalTheory.exists_heightOneSpectrum_natCast_mem D.host.E hpp.1
      have e := congrArg (fun z => ι z P) y.mul_inv
      rw [hy, TensorProduct.tmul_zero, zero_mul, map_zero, map_one] at e
      exact zero_ne_one (α := P.adicCompletion D.host.E) e
    rw [hd' (Units.map (incA D).toMonoidHom (Units.mk0 a ha)) y hy.symm, h.1.2]
  · obtain ⟨x, hx0, hx, hx'⟩ := exists_lift D y
    rw [hd' x y hx]
    exact GlobalTheory.tame_heckeChar_eq_one_of_finUnit D c χ h hδ.tame p hδ.unr x ⟨hx0, hx ▸ hy.1, hx' ▸ hy.2⟩ (hx ▸ hc)
  · obtain ⟨P, hP⟩ := GlobalTheory.exists_heightOneSpectrum_natCast_mem D.host.E hpp.1
    obtain ⟨k, hk, hk1⟩ := exists_unit_ne_one χ P (hδ.tame P) fun hu => by
      have := (hδ.ine P hP 1).1 fun x hx => by rw [hu x hx, one_pow]
      omega
    have hcop : Nat.Coprime p (D.host.g 0 * D.host.g 1) :=
      ((Nat.coprime_primes hpp.1 (D.host.g_prime 0)).2 (hpp.2 0)).mul_right
        ((Nat.coprime_primes hpp.1 (D.host.g_prime 1)).2 (hpp.2 1))
    obtain ⟨e, x, he, hx, i1, i2⟩ := exists_local D P k hk (D.host.g 0 * D.host.g 1) fun hm => by
      obtain ⟨a, b, hab⟩ := (Nat.Coprime.cast (R := 𝓞 D.host.E) hcop)
      exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
        (hab ▸ add_mem (Ideal.mul_mem_left _ _ hP) (Ideal.mul_mem_left _ _ hm)))
    refine ⟨_, i1, i2, fun hh => hk1 (Units.ext ?_)⟩
    rw [← h.2 P e he k x hx, ← hd x, ← hcoe, hh]
  · obtain ⟨x, -, hx, -⟩ := exists_lift D y
    rw [MonoidHom.comp_apply, ← map_pow, hd' x y hx, h1, map_one]
  · obtain ⟨x, -, hx, -⟩ := exists_lift D y
    obtain ⟨z, hz⟩ := hcv x
    rw [hcoe, hd' x y hx, hz]
    exact hval z

end GlobalTheory.TameFinitePart
