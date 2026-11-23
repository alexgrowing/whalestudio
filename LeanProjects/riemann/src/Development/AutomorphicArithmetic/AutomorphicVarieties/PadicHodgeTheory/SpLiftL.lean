import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsFirstOrderDeformationOfRZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.SpFlag
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.SpBorLift
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IotaFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.DecEmb
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LiftSymplecticSimilitudeNilpotent
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LiftUnramifiedUnipotentCharacter
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.HV UpperTheory.V.Base IsLocalRing

private theorem exists_iso {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime]
    (A : ValuationSubring Ω) (hA : A.valuation (l : Ω) < 1) :
    ∃ e : Formalism.BasicNotions.Loc.GQ l ≃* ↥(Dec (F := ℚ) A), Continuous e ∧ Continuous e.symm ∧
      (∀ s, ((e s : ↥(Dec (F := ℚ) A)) : G ℚ Ω) ∈ Ine (F := ℚ) A ↔ s ∈ Iq l) ∧
      ∀ s, cycZ ℚ Ω l ((e s : ↥(Dec (F := ℚ) A)) : G ℚ Ω) = UpperTheory.V.Loc.cyc l l s := by
  obtain ⟨w, hw, hAw⟩ := GlobalTheory.DecLocal.exists_place_below (p := l) (F := ℚ) A hA
  obtain ⟨j, rfl⟩ := (decEmb (F := ℚ) (Ω := Ω) (v := l)).1 A w hAw hw
  obtain ⟨h1, h2, h3, -, h5, -, -⟩ := iotaFacts (Ω := Ω) j
  have hmem : ∀ g, iota j g ∈ Dec (F := ℚ) (placeJ j) := fun g => h2 ▸ ⟨g, rfl⟩
  let f := (iota j).codRestrict (Dec (F := ℚ) (placeJ j)) hmem
  have hf : Topology.IsEmbedding f := h1.codRestrict _ hmem
  have hs : Function.Surjective f := fun g => by
    have : (g : G ℚ Ω) ∈ (iota j).range := by rw [h2]; exact g.2
    obtain ⟨s, hs⟩ := this
    exact ⟨s, Subtype.ext hs⟩
  let e := MulEquiv.ofBijective f ⟨hf.injective, hs⟩
  refine ⟨e, hf.continuous, ?_, fun s => by rw [← h3]; exact Iff.rfl, fun s => DFunLike.congr_fun (h5 l) s⟩
  rw [hf.isInducing.continuous_iff]
  have : (f ∘ e.symm) = id := funext fun g => e.apply_symm_apply g
  rw [this]
  exact continuous_id

private theorem nonres {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    (D : Raw Ω c) (hD : D.Good) :
    (∃ g : D.Gp l, D.al g ≠ chiO ℚ Ω l c.O g) ∧ (∃ g : D.Gp l, D.be g ≠ chiO ℚ Ω l c.O g) ∧
      (∃ g : D.Gp l, D.Psi g ≠ chiO ℚ Ω l c.O g) ∧ ∃ g : D.Gp l, D.th g ≠ chiO ℚ Ω l c.O g := by
  have hl : l ∈ D.T := Finset.mem_insert_self _ _
  have hs : D.sg l ∈ D.Gp l := (hD.sg_frob l hl).1
  have h1 : chiO ℚ Ω l c.O (D.sg l) = 1 := by
    simp only [chiO, MonoidHom.comp_apply, hD.sg_cyc, map_one]
  let R : c.Oˣ →* (ResidueField c.O)ˣ := Units.map (residue c.O : c.O →* ResidueField c.O)
  have h2 : R (D.om (D.sg l)) = 1 := Units.ext (by
    have := hD.om_bar (D.sg l)
    simp only [Raw.bar, h1, Units.val_one, map_one] at this
    exact this)
  have h3 : ∀ i : ℤ, R (D.ξ (D.sg l)) * R (D.Psi (D.sg l)) ^ i ≠ 1 := fun i h =>
    hD.condD l hl i (by
      rw [← map_zpow, ← map_mul] at h
      exact congrArg Units.val h)
  have h4 : R (D.al (D.sg l)) = R (D.ξ (D.sg l)) := by
    simp only [Raw.al, MonoidHom.mul_apply, MonoidHom.inv_apply, map_mul, map_inv, h1, h2, map_one, inv_one, one_mul]
  refine ⟨⟨⟨_, hs⟩, fun h => h3 0 ?_⟩, ⟨⟨_, hs⟩, fun h => h3 (-1) ?_⟩, ⟨D.s0, fun h => hD.decompSigma_ord ?_⟩,
    ⟨_, hs⟩, fun h => h3 1 ?_⟩
  · rw [zpow_zero, mul_one, ← h4, h, h1, map_one]
  · have := congrArg R h
    simp only [Raw.be, MonoidHom.mul_apply, MonoidHom.inv_apply, map_mul, map_inv, h1, h4, map_one] at this
    rw [zpow_neg_one, mul_inv_eq_one.1 this, mul_inv_cancel]
  · have hψ : D.ψ D.s0 = 1 := hD.decompSigma_mem.1.2
    have he := hD.two_le
    simp only [Raw.Psi, UpperTheory.V.Chr.Psi, MonoidHom.mul_apply, hψ, mul_one, zpow_natCast, MonoidHom.pow_apply] at h
    have h5 : chiO ℚ Ω l c.O D.s0 ^ (D.e - 1) = 1 := by
      apply mul_right_cancel (b := chiO ℚ Ω l c.O D.s0)
      rw [← pow_succ, Nat.sub_add_cancel (by omega), h, one_mul]
    refine isOfFinOrder_iff_pow_eq_one.2 ⟨D.e - 1, by omega, Units.ext ?_⟩
    have hi : Function.Injective (algebraMap ℤ_[l] (PadicAlgCl l)) := by
      rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] (PadicAlgCl l)]
      exact (algebraMap ℚ_[l] (PadicAlgCl l)).injective.comp (IsFractionRing.injective ℤ_[l] ℚ_[l])
    have hi' : Function.Injective (algebraMap ℤ_[l] c.O) := fun a b h => hi (congrArg Subtype.val h)
    apply hi'
    have := congrArg Units.val h5
    simpa [chiO] using this
  · have := congrArg R h
    simp only [Raw.th, MonoidHom.mul_apply, map_mul, h1, h4, map_one] at this
    rwa [zpow_one]

section Alg

variable {B : Type} [CommRing B]

private theorem adj_mul (X Y : M4 B) : adj (X * Y) = adj Y * adj X := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four, adj_apply, sgn, Fin.rev] <;> ring

private theorem gsp_conj {ν : B} {h : (M4 B)ˣ} (hh : IsGSp 1 (h : M4 B)) {X : M4 B} (hX : IsGSp ν X) :
    IsGSp ν ((h⁻¹ : (M4 B)ˣ) * X * h) ∧ IsGSp ν (h * X * (h⁻¹ : (M4 B)ˣ)) := by
  have h1 : adj (h : M4 B) = (h⁻¹ : (M4 B)ˣ) := by
    rw [IsGSp, one_smul] at hh
    exact (Units.inv_eq_of_mul_eq_one_left hh).symm
  have h0 : adj (1 : M4 B) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev]
  have h2 : adj ((h⁻¹ : (M4 B)ˣ) : M4 B) = h := by
    have := adj_mul (h : M4 B) (h⁻¹ : (M4 B)ˣ)
    rw [Units.mul_inv, h0, h1] at this
    exact (Units.inv_eq_of_mul_eq_one_left this.symm).symm
  unfold IsGSp at hX ⊢
  constructor
  · rw [adj_mul, adj_mul, h1, h2]
    simp only [mul_assoc, Units.mul_inv_cancel_left]
    rw [← mul_assoc (adj X), hX]
    simp
  · rw [adj_mul, adj_mul, h1, h2]
    simp only [mul_assoc, Units.inv_mul_cancel_left]
    rw [← mul_assoc (adj X), hX]
    simp

private theorem gsp_diag {ν : B} {X : M4 B} (hX : IsGSp ν X) (hl : ∀ i j, j < i → X i j = 0) :
    X 3 3 * X 0 0 = ν ∧ X 2 2 * X 1 1 = ν := by
  have e0 := congrFun (congrFun hX 0) 0
  have e1 := congrFun (congrFun hX 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_four, adj_apply, sgn, Fin.rev, hl 1 0 (by decide), hl 2 0 (by decide),
    hl 3 0 (by decide), hl 2 1 (by decide), hl 3 1 (by decide), hl 3 2 (by decide)] at e0 e1
  exact ⟨e0, e1⟩

private def cj {H : Type} [Group H] (h : (M4 B)ˣ) (r : H →* M4 B) : H →* M4 B where
  toFun g := h * r g * (h⁻¹ : (M4 B)ˣ)
  map_one' := by simp
  map_mul' a b := by simp only [map_mul, mul_assoc, Units.inv_mul_cancel_left]

private theorem cj_cont {H : Type} [Group H] [TopologicalSpace H] [TopologicalSpace B] [IsTopologicalRing B]
    (h : (M4 B)ˣ) (r : H →* M4 B) (hr : ∀ i j, Continuous fun g => r g i j) (i j : Fin 4) :
    Continuous fun g => cj h r g i j := by
  have h1 : Continuous r := continuous_matrix hr
  exact ((continuous_const.matrix_mul h1).matrix_mul continuous_const).matrix_elem i j

private theorem map_cj {B' : Type} [CommRing B'] (p : B →+* B') {h : (M4 B)ˣ} {h' : (M4 B')ˣ}
    (e : (h : M4 B).map p = h') (X : M4 B) :
    ((h : M4 B) * X * (h⁻¹ : (M4 B)ˣ)).map p = h' * X.map p * (h'⁻¹ : (M4 B')ˣ) ∧
      (((h⁻¹ : (M4 B)ˣ) : M4 B) * X * h).map p = (h'⁻¹ : (M4 B')ˣ) * X.map p * h' := by
  have e' : ((h⁻¹ : (M4 B)ˣ) : M4 B).map p = (h'⁻¹ : (M4 B')ˣ) := by
    refine (Units.inv_eq_of_mul_eq_one_right ?_).symm
    rw [← e, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero p) (map_one p)]
  simp only [Matrix.map_mul, e, e', and_self]

private theorem unit_of {E : Type} [Field E] [Algebra E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a)
    {x : B} (hx : π x ≠ 0) : IsUnit x := by
  have h := (hπ (x - algebraMap E B (π x)) (by simp)).isUnit_add_right_of_commute
    ((IsUnit.mk0 _ hx).map (algebraMap E B)) (Commute.all _ _)
  simpa using h

end Alg

theorem UpperTheory.V.Loc.spLiftL :
    LocalPublishedTheorems → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (hD : D.Good) (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra ↥c.O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ↥c.O E] [IsScalarTower ℤ_[l] ℚ_[l] E] [IsFractionRing ↥c.O E] (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra ↥c.O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] ↥c.O B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower ↥c.O E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (B' : Type) [CommRing B'] [Algebra ℚ_[l] B'] [Module.Finite ℚ_[l] B'] [Algebra ↥c.O B'] [Algebra ℤ_[l] B'] [IsScalarTower ℤ_[l] ↥c.O B'] [IsScalarTower ℤ_[l] ℚ_[l] B'] [Algebra E B'] [IsScalarTower ↥c.O E B'] [IsScalarTower ℚ_[l] E B'] (π' : B' →ₐ[E] E) (hπ' : ∀ a, π' a = 0 → IsNilpotent a) (p : B →ₐ[E] B'), Function.Surjective p → π'.comp p = π → ∀ r' : D.Gp l →* M4 B', IsContinuousLiftOfRZero D (π' : B' →+* E) l r' → EqL D r' → ∃ r : D.Gp l →* M4 B, IsContinuousLiftOfRZero D (π : B →+* E) l r ∧ EqL D r ∧ mapRep (p : B →+* B') r = r' := by
  intro hP Ω _ _ _ l _ c D hD E _ _ _ _ _ _ _ _ B _ _ _ _ _ _ _ _ _ _ π hπ B' _ _ _ _ _ _ _ _ _ _ π' hπ' p hp hpπ
    r' hr' hE'
  letI : TopologicalSpace B := moduleTopology ℚ_[l] B
  haveI : IsModuleTopology ℚ_[l] B := ⟨rfl⟩
  haveI : IsTopologicalRing B := IsModuleTopology.isTopologicalRing ℚ_[l] B
  letI : TopologicalSpace B' := moduleTopology ℚ_[l] B'
  haveI : IsModuleTopology ℚ_[l] B' := ⟨rfl⟩
  haveI : IsTopologicalRing B' := IsModuleTopology.isTopologicalRing ℚ_[l] B'
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap ℚ_[l] E).injective
  have hpp : ∀ a, π' (p a) = π a := fun a => DFunLike.congr_fun hpπ a
  have hOB : ∀ x : c.O, algebraMap c.O B x = algebraMap E B (algebraMap c.O E x) := IsScalarTower.algebraMap_apply _ _ _
  have hOB' : ∀ x : c.O, algebraMap c.O B' x = algebraMap E B' (algebraMap c.O E x) :=
    IsScalarTower.algebraMap_apply _ _ _
  have hpO : ∀ x : c.O, p (algebraMap c.O B x) = algebraMap c.O B' x := fun x => by rw [hOB, hOB', p.commutes]
  have hπO : ∀ x : c.O, π' (algebraMap c.O B' x) = algebraMap c.O E x := fun x => by rw [hOB', π'.commutes]; rfl
  obtain ⟨e, hec, hec', heI, hecyc⟩ := exists_iso l (D.pl l) (hD.pl_over l Fact.out)
  obtain ⟨hm', h', κ', hh', hh1', hfl', hκ'⟩ := (spFlag D hD E B' π' hπ' r' hr').1 hE'
  obtain ⟨h, hh, hh1, hhp⟩ := UpperTheory.lift_symplectic_similitude_nilpotent π hπ π' hπ' p hp hpπ h' hh' hh1'
  let T' := cj h'⁻¹ r'
  have hT' : ∀ g, T' g = (h'⁻¹ : (M4 B')ˣ) * r' g * h' := fun g => rfl
  have hTc : ∀ i j, Continuous fun g => T' g i j := cj_cont _ _ hr'.cont
  have hTG : ∀ g : D.Gp l, IsGSp (algebraMap c.O B' (D.th g)) (T' g) := fun g => (gsp_conj hh' (hm' g)).1
  have hTπ : ∀ g, (T' g).map π' = (D.r0At l g).map (algebraMap c.O E) := fun g => by
    have := (map_cj (π' : B' →+* E) (h := h') (h' := 1) hh1' (r' g)).2
    rw [inv_one, Units.val_one, one_mul, mul_one] at this
    exact this.trans (DFunLike.congr_fun hr'.red g)
  have hκT : ∀ i g, (κ' i g : B') = T' g i i := fun i g => ((hfl' g).2 i).symm
  have hκπ : ∀ i (g : D.Gp l), π' (κ' i g) = algebraMap c.O E (D.ps i g) := fun i g => by
    have := congrFun (congrFun (hTπ g) i) i
    rw [hκT]
    simpa [Raw.r0, diagRep] using this
  have hκc : ∀ i, Continuous fun g => (κ' i g : B') := fun i => by simpa only [hκT] using hTc i i
  let P : Fin 4 → D.Gp l →* Bˣ := fun i =>
    (Units.map (algebraMap c.O B : c.O →* B)).comp ((D.ps i).comp (D.Gp l).subtype)
  have hPv : ∀ i (g : D.Gp l), (P i g : B) = algebraMap c.O B (D.ps i g) := fun _ _ => rfl
  have hPc : ∀ i, Continuous fun g => (P i g : B) := fun i => by
    let σ : B' →ₗ[ℚ_[l]] B := ((IsScalarTower.toAlgHom ℚ_[l] E B).comp (π'.restrictScalars ℚ_[l])).toLinearMap
    have : (fun g => (P i g : B)) = fun g => σ (κ' i g) := funext fun g => by
      rw [hPv, hOB, ← hκπ]; rfl
    rw [this]
    exact (IsModuleTopology.continuous_of_linearMap σ).comp (hκc i)
  have hpc : Continuous p := IsModuleTopology.continuous_of_linearMap (p.restrictScalars ℚ_[l]).toLinearMap
  have hinv : ∀ {R : Type} [CommRing R] [TopologicalSpace R] (k : D.Gp l →* Rˣ), Continuous (fun g => (k g : R)) →
      Continuous fun g => ((k⁻¹ g : Rˣ) : R) := fun k hk => by
    simp only [MonoidHom.inv_apply, ← map_inv]
    exact hk.comp continuous_inv
  have hlift : ∀ i, ∃ k : D.Gp l →* Bˣ, Continuous (fun g => (k g : B)) ∧
      (∀ s : D.Gp l, (s : G ℚ Ω) ∈ D.Ip l → k s = P i s) ∧ ∀ g, Units.map (p : B →* B') (k g) = κ' i g := fun i => by
    let w' : D.Gp l →* B'ˣ := κ' i * (Units.map (p : B →* B')).comp (P i)⁻¹
    have hw' : ∀ g, (w' g : B') = κ' i g * p ((P i)⁻¹ g : Bˣ) := fun _ => rfl
    have hPP : ∀ g, p (P i g : Bˣ) * p ((P i)⁻¹ g : Bˣ) = 1 := fun g => by
      rw [← map_mul, MonoidHom.inv_apply, Units.mul_inv, map_one]
    obtain ⟨u, hu, huI, hup⟩ := UpperTheory.lift_unramified_unipotent_character (p.restrictScalars ℚ_[l]) hp
      (fun a ha => hπ a (by rw [← hpp, show p a = 0 from ha, map_zero])) (w'.comp e.toMonoidHom)
      (((hκc i).mul (hpc.comp (hinv _ (hPc i)))).comp hec)
      (fun g hg => Units.ext (by
        change (w' (e g) : B') = 1
        rw [hw', hκ' i _ ((heI g).2 hg), ← hpO, ← hPv, hPP]))
      (fun g => hπ' _ (by
        change π' ((w' (e g) : B') - 1) = 0
        rw [hw', ← hPP (e g), map_sub, map_mul, map_mul, hκπ, hPv, hpO, hπO, sub_self]))
    refine ⟨P i * u.comp e.symm.toMonoidHom, (hPc i).mul (Continuous.comp (g := fun g => (u g : B)) hu hec'), fun s hs => ?_, fun g => ?_⟩
    · change P i s * u (e.symm s) = _
      rw [huI _ ((heI _).1 (by rwa [e.apply_symm_apply])), mul_one]
    · apply Units.ext
      change p (P i g * u (e.symm g) : B) = _
      have : p (u (e.symm g) : B) = w' (e (e.symm g)) := hup (e.symm g)
      rw [map_mul, this, e.apply_symm_apply, hw', mul_left_comm, hPP, mul_one]
  obtain ⟨k2, c2, i2, p2⟩ := hlift 2
  obtain ⟨k3, c3, i3, p3⟩ := hlift 3
  let κ : Fin 4 → D.Gp l →* Bˣ := ![P 0 * k3⁻¹, P 0 * k2⁻¹, k2, k3]
  have hκp : ∀ i g, Units.map (p : B →* B') (κ i g) = κ' i g := fun i g => by
    obtain ⟨e0, e1⟩ := gsp_diag (hTG g) (hfl' g).1
    rw [← hκT, ← hκT, ← hpO] at e0 e1
    have e0' : κ' 3 g * κ' 0 g = Units.map (p : B →* B') (P 0 g) := Units.ext e0
    have e1' : κ' 2 g * κ' 1 g = Units.map (p : B →* B') (P 0 g) := Units.ext e1
    fin_cases i
    · change Units.map (p : B →* B') (P 0 g * (k3 g)⁻¹) = κ' 0 g
      rw [map_mul, map_inv, p3, ← e0', mul_inv_cancel_comm]
    · change Units.map (p : B →* B') (P 0 g * (k2 g)⁻¹) = κ' 1 g
      rw [map_mul, map_inv, p2, ← e1', mul_inv_cancel_comm]
    · exact p2 g
    · exact p3 g
  have hκI : ∀ i (s : D.Gp l), (s : G ℚ Ω) ∈ D.Ip l → κ i s = P i s := fun i s hs => by
    have e3 : P 3 s = 1 := map_one (Units.map (algebraMap c.O B : c.O →* B))
    have e0 : P 0 s = P 2 s * P 1 s := map_mul (Units.map (algebraMap c.O B : c.O →* B)) _ _
    fin_cases i
    · change P 0 s * (k3 s)⁻¹ = P 0 s
      rw [i3 s hs, e3, inv_one, mul_one]
    · change P 0 s * (k2 s)⁻¹ = P 1 s
      rw [i2 s hs, e0, mul_inv_cancel_comm]
    · exact i2 s hs
    · exact i3 s hs
  let Rd : Bˣ →* Eˣ := Units.map (π : B →* E)
  let Re : c.Oˣ →* Eˣ := Units.map (algebraMap c.O E : c.O →* E)
  have hRd : ∀ i (g : D.Gp l), Rd (κ i g) = Re (D.ps i g) := fun i g => Units.ext (by
    change π (κ i g) = algebraMap c.O E (D.ps i g)
    rw [← hκπ, ← hκp, ← hpp]
    rfl)
  let α : D.Gp l →* Bˣ := k2 * k3⁻¹
  let β : D.Gp l →* Bˣ := P 0 * k2⁻¹ * k2⁻¹
  have hα : ∀ g : D.Gp l, Rd (α g) = Re (D.al g) := fun g => by
    change Rd (κ 2 g * (κ 3 g)⁻¹) = _
    rw [map_mul, map_inv, hRd, hRd]
    simp [Raw.ps]
  have hβ : ∀ g : D.Gp l, Rd (β g) = Re (D.be g) := fun g => by
    change Rd (κ 1 g * (κ 2 g)⁻¹) = _
    rw [map_mul, map_inv, hRd, hRd]
    simp [Raw.ps, Raw.be]
  have hun : ∀ (x : Bˣ) (γ : G ℚ Ω →* c.Oˣ) (g : D.Gp l), Rd x = Re (γ g) → γ g ≠ chiO ℚ Ω l c.O g →
      IsUnit ((x : B) - algebraMap ℚ_[l] B ((UpperTheory.V.Loc.cyc l l (e.symm g) : ℤ_[l]ˣ) : ℤ_[l])) := by
    intro x γ g h1 h2
    refine unit_of π hπ fun h3 => h2 (Units.ext (IsFractionRing.injective c.O E ?_))
    have h4 : π x = algebraMap c.O E (γ g) := congrArg Units.val h1
    rw [map_sub, sub_eq_zero, h4, ← hecyc, e.apply_symm_apply, IsScalarTower.algebraMap_apply ℚ_[l] E B,
      π.commutes] at h3
    rw [h3]
    change algebraMap ℚ_[l] E (algebraMap ℤ_[l] ℚ_[l] _) = algebraMap c.O E (algebraMap ℤ_[l] c.O _)
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have hdiag : ∀ g i, ![(α g : B) * α g * β g * k3 g, α g * β g * k3 g, α g * k3 g, k3 g] i = κ i g := fun g i => by
    fin_cases i
    · have : α g * α g * β g * k3 g = P 0 g * (k3 g)⁻¹ := by
        simp only [α, β, MonoidHom.mul_apply, MonoidHom.inv_apply]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel
      exact congrArg Units.val this
    · have : α g * β g * k3 g = P 0 g * (k2 g)⁻¹ := by
        simp only [α, β, MonoidHom.mul_apply, MonoidHom.inv_apply]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel
      exact congrArg Units.val this
    · exact congrArg Units.val (inv_mul_cancel_right (k2 g) (k3 g))
    · rfl
  obtain ⟨⟨g1, n1⟩, ⟨g2, n2⟩, ⟨g3, n3⟩, g4, n4⟩ := nonres D hD
  obtain ⟨T, cT, lT, dT, gT, pT⟩ := borLift hP e.symm.toMonoidHom
    (Homeomorph.mk e.symm.toEquiv hec' hec).isOpenEmbedding (p.restrictScalars ℚ_[l]) hp
    ((Units.coeHom B).comp α) ((Units.coeHom B).comp β) ((Units.coeHom B).comp k3) (c2.mul (hinv _ c3))
    (((hPc 0).mul (hinv _ c2)).mul (hinv _ c2)) c3
    (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      refine ⟨⟨g1, hun _ _ _ (hα g1) n1⟩, ⟨g2, hun _ _ _ (hβ g2) n2⟩, ⟨g3, hun (α g3 * β g3) _ _ ?_ n3⟩,
        g4, hun (α g4 * α g4 * β g4) _ _ ?_ n4⟩
      · rw [map_mul, hα, hβ, ← map_mul]
        simp [Raw.be]
      · rw [map_mul, map_mul, hα, hβ, ← map_mul, ← map_mul]
        simp [Raw.be, Raw.th, mul_assoc])
    T' hTc (fun g => (hfl' g).1)
    (fun g i => by
      rw [← hκT, ← hκp]
      exact congrArg p (hdiag g i).symm)
    (fun g => ⟨_, hTG g⟩)
  have hred : mapRep (p : B →+* B') (cj h T) = r' := MonoidHom.ext fun g => by
    refine (map_cj (p : B →+* B') hhp (T g)).1.trans ?_
    have : (T g).map (p : B →+* B') = T' g := pT g
    rw [this, hT']
    simp only [mul_assoc, Units.mul_inv_cancel_left, Units.mul_inv, mul_one]
  have hL : IsContinuousLiftOfRZero D (π : B →+* E) l (cj h T) := ⟨by
    rw [← hr'.red, ← hred]
    ext g a b
    exact (hpp _).symm, cj_cont _ _ cT⟩
  refine ⟨cj h T, hL, (spFlag D hD E B π hπ _ hL).2 ⟨fun g => (gsp_conj hh ?_).2, h, κ, hh, hh1, fun g => ?_,
    fun i s hs => congrArg Units.val (hκI i s hs)⟩, hred⟩
  · have e1 : (α g : B) * α g * β g * k3 g * k3 g = algebraMap c.O B (D.th g) := by
      rw [show (α g : B) * α g * β g * k3 g = κ 0 g from hdiag g 0]
      exact congrArg Units.val (inv_mul_cancel_right (P 0 g) (k3 g))
    rw [← e1]
    exact gT g
  · have : ((h⁻¹ : (M4 B)ˣ) * cj h T g * h : M4 B) = T g := by
      change ((h⁻¹ : (M4 B)ˣ) * (h * T g * (h⁻¹ : (M4 B)ˣ)) * h : M4 B) = T g
      simp only [mul_assoc, Units.inv_mul_cancel_left, Units.inv_mul, mul_one]
    rw [this]
    exact ⟨lT g, fun i => (dT g i).trans (hdiag g i)⟩
