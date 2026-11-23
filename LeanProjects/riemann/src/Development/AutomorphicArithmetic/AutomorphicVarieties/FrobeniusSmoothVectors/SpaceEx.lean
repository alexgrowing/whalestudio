import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.RbarProd
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.OrdOfFlag
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.UnivLift
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MonomialRepresentations.HenselDiag
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.PhiSub

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

section
variable {H C : Type} [CommRing C] {n : ℕ}

private theorem conj_prod {R : Type} [Monoid R] (P Q : R) (h : P * Q = 1) (h' : Q * P = 1) (L : List R) :
    (L.map fun x => Q * x * P).prod = Q * L.prod * P := by
  induction L with
  | nil => simp [h']
  | cons a L ih =>
    rw [List.map_cons, List.prod_cons, ih, List.prod_cons]
    simp only [mul_assoc]
    rw [← mul_assoc P Q, h, one_mul]

private theorem ord_conj (r : H → Matrix (Fin n) (Fin n) C) (ψ : Fin n → H → C) (P Q : Matrix (Fin n) (Fin n) C)
    (h : P * Q = 1) (g : Fin n → H) (ho : ordProd r ψ g = 0) : ordProd (fun s => Q * r s * P) ψ g = 0 := by
  have h' : Q * P = 1 := mul_eq_one_comm.1 h
  have := conj_prod P Q h h' (List.ofFn fun i => r (g i) - ψ i (g i) • (1 : Matrix (Fin n) (Fin n) C))
  unfold ordProd at ho ⊢
  rw [ho, mul_zero, zero_mul, List.map_ofFn] at this
  rw [← this]
  congr 2
  funext i
  simp [mul_sub, sub_mul, h']

private theorem tri_diag (hn : n = 2 ∨ n = 3) (T : H → Matrix (Fin n) (Fin n) C) (ψ : Fin n → H → C) (g₀ : H)
    (d : Fin n → C) (hd : T g₀ = diagonal d) (hu : ∀ i j, i ≠ j → IsUnit (d i - ψ j g₀))
    (ho : ∀ g, ordProd T ψ g = 0) (s : H) (a b : Fin n) (hab : b ≤ a) :
    (T s - ψ a s • (1 : Matrix (Fin n) (Fin n) C)) a b = 0 := by
  have e : ∀ j, T g₀ - ψ j g₀ • (1 : Matrix (Fin n) (Fin n) C) = diagonal fun i => d i - ψ j g₀ := fun j => by
    rw [hd]
    ext x y
    by_cases h : x = y <;> simp [h, Matrix.one_apply]
  have h := congrFun (congrFun (ho (Function.update (fun _ => g₀) a s)) a) b
  have k : ∀ i j, i ≠ j → ∀ x, ((d i - ψ j g₀) * x = 0 ↔ x = 0) ∧ (x * (d i - ψ j g₀) = 0 ↔ x = 0) :=
    fun i j hij x => ⟨(hu i j hij).mul_right_eq_zero, (hu i j hij).mul_left_eq_zero⟩
  unfold ordProd at h
  rcases hn with rfl | rfl
  · fin_cases a <;> fin_cases b <;> simp at hab <;>
      simp [List.ofFn_succ, e, k, -Matrix.sub_apply] at h <;> exact h
  · fin_cases a <;> fin_cases b <;> simp at hab <;>
      simp [List.ofFn_succ, e, k, -Matrix.sub_apply, ← mul_assoc] at h <;>
      (try simp [k, mul_assoc, -Matrix.sub_apply] at h) <;> exact h

private theorem ord_of_tri [Group H] (r : H →* Matrix (Fin n) (Fin n) C) (P Q : Matrix (Fin n) (Fin n) C)
    (h : P * Q = 1) (ht : ∀ s i j, j < i → (Q * r s * P) i j = 0) :
    ∃ ψ : Fin n → H →* Cˣ, (∀ i s, (ψ i s : C) = (Q * r s * P) i i) ∧
      ∀ g, ordProd r (fun i s => (ψ i s : C)) g = 0 := by
  have h' : Q * P = 1 := mul_eq_one_comm.1 h
  let χ : Fin n → H →* C := fun i =>
    { toFun := fun s => (Q * r s * P) i i
      map_one' := by simp [h']
      map_mul' := fun s t => by
        have : Q * r (s * t) * P = (Q * r s * P) * (Q * r t * P) := by
          simp only [map_mul, mul_assoc]
          rw [← mul_assoc P Q, h, one_mul]
        rw [this, Matrix.mul_apply]
        refine Finset.sum_eq_single i (fun j _ hj => ?_) (by simp)
        rcases lt_or_gt_of_ne hj with k | k
        · rw [ht s i j k, zero_mul]
        · rw [ht t j i k, mul_zero] }
  exact ⟨fun i => (χ i).toHomUnits, fun _ _ => rfl,
    (ord_of_flag r _ ⟨⟨Q, P, h', h⟩, fun s => ⟨ht s, fun _ => rfl⟩⟩).1⟩

private theorem lc_mat {K : Type} [TopologicalSpace H] (M : H → Matrix (Fin n) (Fin n) K)
    (h : ∀ i j, IsLocallyConstant fun s => M s i j) : IsLocallyConstant M := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
  have := Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun b => (h a b).eventually_eq x
  filter_upwards [this] with y hy
  exact Matrix.ext hy

private theorem cont_conj [TopologicalSpace H] (I : Ideal C) (M : H → Matrix (Fin n) (Fin n) C)
    (P Q : Matrix (Fin n) (Fin n) C) (h : ∀ i j, AdicCont I fun s => M s i j) (i j : Fin n) :
    AdicCont I fun s => (Q * M s * P) i j := fun N => by
  have := (lc_mat (fun s => (Ideal.Quotient.mk (I ^ N)).mapMatrix (M s)) fun a b => h a b N).comp
    fun X => ((Ideal.Quotient.mk (I ^ N)).mapMatrix Q * X * (Ideal.Quotient.mk (I ^ N)).mapMatrix P) i j
  convert this using 1
  funext s
  simp only [Function.comp_apply, ← map_mul]
  rfl

end

private theorem w_inj {k : Type} [Field k] {n : ℕ} (hn : n = 2 ∨ n = 3) (x : kˣ) (hx : x ^ 2 ≠ 1) (i j : Fin n)
    (hij : i ≠ j) : ((x ^ w n i : kˣ) : k) ≠ ((x ^ w n j : kˣ) : k) := by
  intro h
  have h1 : x ^ (w n i - w n j) = 1 := by rw [_root_.zpow_sub, Units.ext h, mul_inv_cancel]
  have h2 : w n i - w n j ∣ 2 := by
    clear h h1
    revert i j
    rcases hn with rfl | rfl <;> decide
  obtain ⟨m, hm⟩ := h2
  apply hx
  rw [← _root_.zpow_natCast, Nat.cast_ofNat, hm, _root_.zpow_mul, h1, _root_.one_zpow]

private theorem diag_ex {O R : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (a : Fin n → ResidueField O) (ha : ∀ i j, i ≠ j → a i ≠ a j)
    (hM : (res O R).mapMatrix M = diagonal a) :
    ∃ (P Q : Matrix (Fin n) (Fin n) R) (d : Fin n → R), P * Q = 1 ∧ (res O R).mapMatrix P = 1 ∧
      (res O R).mapMatrix Q = 1 ∧ Q * M * P = diagonal d := by
  haveI : HenselianLocalRing R := ⟨fun f hf a₀ h1 h2 => HenselianRing.is_henselian f hf a₀ h1 (h2.map _)⟩
  have hu : ∀ x : R, res O R x ≠ 0 → IsUnit x := fun x hx => by
    by_contra h
    exact hx ((res_eq_zero_iff O R x).2 h)
  have hM' : ∀ i j, res O R (M i j) = diagonal a i j := fun i j => congrFun (congrFun hM i) j
  obtain ⟨P, d, h1, h2, -⟩ := UpperTheory.V.AlgebraTools.henselDiag R (Fin n) M
    (fun i j h => by rw [← res_eq_zero_iff O, hM', diagonal_apply_ne _ h])
    (fun i j h => hu _ (by rw [map_sub, hM', hM', diagonal_apply_eq, diagonal_apply_eq]; exact sub_ne_zero.2 (ha i j h)))
  have h3 : (res O R).mapMatrix P = 1 := by
    rw [← map_one (res O R).mapMatrix, ← sub_eq_zero, ← map_sub]
    exact Matrix.ext fun i j => (res_eq_zero_iff O R _).2 (h1 i j)
  have h4 : IsUnit P := by
    rw [Matrix.isUnit_iff_isUnit_det]
    apply hu
    rw [AlgHom.map_det, h3, det_one]
    exact one_ne_zero
  obtain ⟨Q, hQ⟩ := h4.exists_right_inv
  refine ⟨P, Q, d, hQ, h3, ?_, ?_⟩
  · have := congrArg (res O R).mapMatrix hQ
    rwa [map_mul, h3, one_mul, map_one] at this
  · rw [mul_assoc, h2, ← mul_assoc, mul_eq_one_comm.1 hQ, one_mul]

theorem UpperTheory.V.Fr.space_ex :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → Nonempty (Space O F n) := by
  intro l _ O _ _ _ _ F C₀ n hF hn
  obtain ⟨ρ₀, hb, hdg⟩ := rbar (n := n) hF
  have hr0 : ∀ g, ρ₀.r g = diagonal fun i => ((F.Ψ g ^ w n i : (ResidueField O)ˣ) : ResidueField O) := fun g => by
    ext i j
    by_cases h : i = j
    · subst h
      rw [diagonal_apply_eq]
      exact hb.1 g i
    · rw [diagonal_apply_ne _ h, hdg g i j h]
  have hΨ : IsLocallyConstant F.Ψ := by
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
    have : IsOpen ((fun y => x⁻¹ * y) ⁻¹' (F.Ψ.ker : Set F.Γ)) := hF.Ψ_open.preimage (by fun_prop)
    filter_upwards [this.mem_nhds (show x ∈ _ by simp)] with y hy
    have h : F.Ψ (x⁻¹ * y) = 1 := hy
    rwa [map_mul, map_inv, inv_mul_eq_one, eq_comm] at h
  have hc : IsLocallyConstant ρ₀.r := by
    rw [show (ρ₀.r : F.G0 → _) = _ from funext hr0]
    exact (hΨ.comp_continuous continuous_subtype_val).comp
      fun x => diagonal fun i => ((x ^ w n i : (ResidueField O)ˣ) : ResidueField O)
  haveI : CompactSpace F.G0 := isCompact_iff_compactSpace.1 (F.del.ker.isClosed_of_isOpen hF.del_open).isCompact
  obtain ⟨R, _, _, _, u, hu⟩ := univ_lift l O F.G0 (Fin n) ρ₀.r (Pa.Det.phiSub l _ hF.del_open hF.phi) hc
  have hres : ∀ g, (res O R).mapMatrix (u.hom g) = ρ₀.r g := fun g => Matrix.ext (u.red g)
  choose g₀ hg₀ using hF.f3
  choose P Q d hPQ hP hQ hd using fun v => diag_ex (u.hom (F.loc0 v (g₀ v))) _
    (w_inj hn _ (hg₀ v)) ((hres _).trans (hr0 _))
  let T : ∀ v, F.Gv v → Matrix (Fin n) (Fin n) R := fun v s => Q v * u.hom (F.loc0 v s) * P v
  have hT : ∀ v s, (res O R).mapMatrix (T v s) = ρ₀.r (F.loc0 v s) := fun v s => by
    rw [map_mul, map_mul, hP, hQ, hres, one_mul, mul_one]
  have hTd : ∀ v s i, res O R (T v s i i) = ((F.Ψ (F.loc v s) ^ w n i : (ResidueField O)ˣ) : ResidueField O) :=
    fun v s i => (congrFun (congrFun (hT v s) i) i).trans (hb.1 _ i)
  let A : F.G0 → Matrix (Fin n) (Fin n) R := fun g => u.hom (F.star g) - Jmat R n * (u.hom g)ᵀ * Jmat R n
  let S : Set R := {x | (∃ g i j, x = A g i j) ∨ (∃ i j, i ≠ j ∧ x = (u.hom F.g0 - u.hom (F.star F.g0)) i j) ∨
    ∃ v s i j, j < i ∧ x = T v s i j}
  have hA : ∀ (C : Type) [CommRing C] [Algebra O C] (f : R →ₐ[O] C) (g : F.G0), f.mapMatrix (A g) =
      f.mapMatrix (u.hom (F.star g)) - Jmat C n * (f.mapMatrix (u.hom g))ᵀ * Jmat C n := fun C _ _ f g => by
    have hJ : f.mapMatrix (Jmat R n) = Jmat C n := Jmat_map (f : R →+* C) n
    rw [map_sub, map_mul, map_mul, hJ]
    rfl
  have hI : ∀ (C : Type) [CommRing C] [Algebra O C] (f : R →ₐ[O] C) (ρ : NRep F n C),
      (∀ g, f.mapMatrix (u.hom g) = ρ.r g) → (∀ v s i j, j < i → f (T v s i j) = 0) → ∀ x ∈ Ideal.span S, f x = 0 := by
    intro C _ _ f ρ h1 h2
    refine (Ideal.span_le (I := RingHom.ker f)).2 ?_
    rintro _ (⟨g, i, j, rfl⟩ | ⟨i, j, h, rfl⟩ | ⟨v, s, i, j, h, rfl⟩)
    · have := hA C f g
      rw [h1, h1, ← ρ.pol, sub_self] at this
      exact congrFun (congrFun this i) j
    · have := ρ.diag i j h
      rwa [← h1, ← h1, ← map_sub] at this
    · exact h2 v s i j h
  have h0 := hI _ (res O R) ρ₀ hres fun v s i j h => (congrFun (congrFun (hT v s) i) j).trans (hdg _ i j h.ne')
  haveI : Nontrivial (R ⧸ Ideal.span S) := Ideal.Quotient.nontrivial_iff.2 fun e => by
    simpa using h0 1 (e ▸ Submodule.mem_top)
  let p := Ideal.Quotient.mkₐ O (Ideal.span S)
  haveI : IsCO O (R ⧸ Ideal.span S) := co_quot O R _ p (Ideal.Quotient.mkₐ_surjective O _)
  have hp : ∀ x ∈ S, p x = 0 := fun x hx => Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span hx)
  have hTf : ∀ (C : Type) [CommRing C] [Algebra O C] (f : R →ₐ[O] C) v s i j,
      (f.mapMatrix (Q v) * f.mapMatrix (u.hom (F.loc0 v s)) * f.mapMatrix (P v)) i j = f (T v s i j) :=
    fun C _ _ f v s i j => by
      rw [← map_mul, ← map_mul]
      rfl
  have hPQf : ∀ (C : Type) [CommRing C] [Algebra O C] (f : R →ₐ[O] C) v,
      f.mapMatrix (P v) * f.mapMatrix (Q v) = 1 := fun C _ _ f v => by rw [← map_mul, hPQ, map_one]
  choose ψ hψ ho using fun v => ord_of_tri ((u.map p).hom.comp (F.loc0 v)) _ _ (hPQf _ p v)
    fun s i j h => (hTf _ p v s i j).trans (hp _ (Or.inr (Or.inr ⟨v, s, i, j, h, rfl⟩)))
  have hψ' : ∀ v i s, (ψ v i s : R ⧸ Ideal.span S) = p (T v s i i) := fun v i s => (hψ v i s).trans (hTf _ p v s i i)
  let ρ : NRep F n (R ⧸ Ideal.span S) :=
    { r := (u.map p).hom
      ψ := ψ
      pol := fun g => sub_eq_zero.1 ((hA _ p g).symm.trans (Matrix.ext fun i j => hp _ (Or.inl ⟨g, i, j, rfl⟩)))
      diag := fun i j h => (map_sub p _ _).symm.trans (hp _ (Or.inr (Or.inl ⟨i, j, h, rfl⟩)))
      ord := ho }
  refine ⟨⟨R ⧸ Ideal.span S, ρ, ⟨⟨(u.map p).cont, fun v i => ?_⟩, ⟨fun g i => ?_, fun v i s => ?_⟩, fun g i j h => ?_⟩,
    fun C _ _ _ ρ' ⟨⟨c1, c2⟩, ⟨b1, b2⟩, b3⟩ => ?_⟩⟩
  · have := cont_conj _ (fun s => (u.map p).hom (F.loc0 v s)) (p.mapMatrix (P v)) (p.mapMatrix (Q v))
      (fun a b N => ((u.map p).cont a b N).comp_continuous (hF.loc_cont v)) i i
    exact (funext (hψ v i)).symm ▸ this
  · exact ((u.map p).red g i i).trans (hb.1 g i)
  · show res O _ (ψ v i s : R ⧸ Ideal.span S) = _
    rw [hψ', res_map, hTd]
    rfl
  · exact ((u.map p).red g i j).trans (hdg g i j h)
  · let r' : Lift O ρ₀.r C := ⟨ρ'.r, c1, fun g i j => by
      by_cases h : i = j
      · subst h
        exact (b1 g i).trans (hb.1 g i).symm
      · exact (b3 g i j h).trans (hdg g i j h).symm⟩
    obtain ⟨f, hf, hfu⟩ := (hu C).2 r' trivial
    have hf' : ∀ g, f.mapMatrix (u.hom g) = ρ'.r g := fun g => congrArg (fun x : Lift O ρ₀.r C => x.hom g) hf
    have key : ∀ v s a b, b ≤ a →
        (f.mapMatrix (T v s) - (ρ'.ψ v a s : C) • (1 : Matrix (Fin n) (Fin n) C)) a b = 0 := fun v => by
      refine tri_diag hn (fun s => f.mapMatrix (T v s)) (fun i s => (ρ'.ψ v i s : C)) (g₀ v) (fun i => f (d v i))
        ?_ (fun i j h => ?_) fun g => ?_
      · show f.mapMatrix (Q v * _ * P v) = _
        rw [hd, AlgHom.mapMatrix_apply, diagonal_map (map_zero f)]
      · by_contra hne
        have h1 := (res_eq_zero_iff O C _).2 hne
        have h2 : d v i = T v (g₀ v) i i := by
          show _ = (Q v * u.hom (F.loc0 v (g₀ v)) * P v : Matrix _ _ R) i i
          rw [hd, diagonal_apply_eq]
        rw [map_sub, res_map, h2, hTd, sub_eq_zero] at h1
        exact w_inj hn _ (hg₀ v) i j h (h1.trans (b2 v j _))
      · have := ord_conj _ _ _ _ (hPQf C f v) g (ρ'.ord v g)
        simpa only [← hf', ← map_mul] using this
    have k1 := hI C f ρ' hf' fun v s i j h => by simpa [h.ne'] using key v s i j h.le
    have k2 : ∀ v i s, f (T v s i i) = ρ'.ψ v i s := fun v i s => by simpa [sub_eq_zero] using key v s i i le_rfl
    refine ⟨Ideal.Quotient.liftₐ _ f k1, NRep.ext (MonoidHom.ext hf') ?_, fun g hg => ?_⟩
    · funext v i
      ext s
      rw [NRep.map_ψ, ← k2]
      exact congrArg (Ideal.Quotient.liftₐ _ f k1) (hψ' v i s)
    · have : g.comp p = f := hfu _ (Lift.ext (congrArg NRep.r hg))
      exact Ideal.Quotient.algHom_ext _ this
