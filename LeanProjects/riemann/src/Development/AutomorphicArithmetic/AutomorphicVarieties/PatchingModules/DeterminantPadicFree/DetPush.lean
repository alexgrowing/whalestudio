import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.ExtFree
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.ZlUniq
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem mapL {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (j : A →+* B) (p : B →+ A)
    (hp : ∀ a y, p (j a * y) = a * p y) (M : Matrix (Fin n) (Fin n) A) (Z : Matrix (Fin n) (Fin n) B) :
    (M.map j * Z).map p = M * Z.map p := by
  ext a b
  simp [Matrix.mul_apply, map_sum, hp]

private theorem mapR {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (j : A →+* B) (p : B →+ A)
    (hp : ∀ a y, p (j a * y) = a * p y) (M : Matrix (Fin n) (Fin n) A) (Z : Matrix (Fin n) (Fin n) B) :
    (Z * M.map j).map p = Z.map p * M := by
  ext a b
  simp only [Matrix.mul_apply, map_sum, Matrix.map_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [mul_comm, hp, mul_comm]

private def ddJ {A B : Type} [CommRing A] [CommRing B] (g : ℕ) (j : A →+* B) : DD A g →+* DD B g where
  toFun d := ⟨j d.a, fun i => j (d.ep i), fun i => j (d.ep' i), j d.eta⟩
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp
  map_mul' x y := by ext <;> simp

private def ddP {A B : Type} [CommRing A] [CommRing B] (g : ℕ) (p : B →+ A) : DD B g →+ DD A g where
  toFun d := ⟨p d.a, fun i => p (d.ep i), fun i => p (d.ep' i), p d.eta⟩
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp

private theorem map_additive_mem_symmetric_deformation {A B : Type} [CommRing A] [CommRing B] {g n a : ℕ} (p : B →+ A)
    (Z : Matrix (Fin n) (Fin n) (DD B g)) (hZ : Z ∈ pairedDualFirstOrderDualMatrixSpace n B B g a) : Z.map (ddP g p) ∈ pairedDualFirstOrderDualMatrixSpace n A A g a := by
  have key : ∀ (b1 b2 b3 b4 : Bool) (y : DD B g), y ∈ ddPart B B g b1 b2 b3 b4 →
      ddP g p y ∈ ddPart A A g b1 b2 b3 b4 := by
    rintro b1 b2 b3 b4 y ⟨h1, h2, h3, h4⟩
    refine ⟨fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_⟩
    · change p y.a = 0
      rw [h1 e, map_zero]
    · funext i
      change p (y.ep i) = 0
      rw [h2 e]; exact map_zero p
    · funext i
      change p (y.ep' i) = 0
      rw [h3 e]; exact map_zero p
    · change p y.eta = 0
      rw [h4 e, map_zero]
  exact fun r s => ⟨fun e => key _ _ _ _ _ ((hZ r s).1 e), fun e => key _ _ _ _ _ ((hZ r s).2 e)⟩

private theorem sum_dd {X ι : Type} [CommRing X] {g : ℕ} (s : Finset ι) (f : ι → DD X g) :
    ∑ i ∈ s, f i = ⟨∑ i ∈ s, (f i).a, fun j => ∑ i ∈ s, (f i).ep j, fun j => ∑ i ∈ s, (f i).ep' j,
      ∑ i ∈ s, (f i).eta⟩ := by
  classical
  induction s using Finset.induction_on with
  | empty => ext <;> simp
  | insert i s hi ih => ext <;> simp [Finset.sum_insert hi, ih]

private theorem exJP {A B : Type} [CommRing A] [CommRing B] {g g' n a m : ℕ} (e : g' = g) (j : A →+* B)
    (b : Fin m → B) (p : Fin m → B →+ A) (hb : ∀ y, y = ∑ i, j (p i y) * b i)
    (hp : ∀ i a y, p i (j a * y) = a * p i y) :
    ∃ (J : DD A g →+* DD B g') (P : Fin m → DD B g' →+ DD A g),
      (∀ c, J (DD.C c) = DD.C (j c)) ∧
      (∀ K : Fin g → Matrix (Fin n) (Fin n) A, (DD.epM K).map J = DD.epM fun i => (K (Fin.cast e i)).map j) ∧
      (∀ i a y, P i (J a * y) = a * P i y) ∧ (∀ y, y = ∑ i, J (P i y) * DD.C (b i)) ∧
      (∀ i y, (P i y).eta = p i y.eta) ∧
      (∀ i Z, Z ∈ pairedDualFirstOrderDualMatrixSpace n B B g' a → Z.map (P i) ∈ pairedDualFirstOrderDualMatrixSpace n A A g a) ∧
      ∀ Z, Z ∈ pairedDualFirstOrderDualMatrixSpace n A A g a → Z.map J ∈ pairedDualFirstOrderDualMatrixSpace n B B g' a := by
  subst e
  refine ⟨ddJ _ j, fun i => ddP _ (p i), fun c => ?_, fun K => ?_, fun i a y => ?_, fun y => ?_, fun _ _ => rfl,
    fun i Z h => map_additive_mem_symmetric_deformation (p i) Z h, fun Z h => map_additive_mem_symmetric_deformation j.toAddMonoidHom Z h⟩
  · ext <;> simp [ddJ]
  · ext <;> simp [ddJ, DD.epM]
  · ext <;> simp [ddJ, ddP, hp]
  · rw [sum_dd]
    ext <;> simp [ddJ, ddP, ← hb]

theorem UpperTheory.V.Pa.Det.detPush :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x x' : NP F n) (j : x.A →+* x'.A), x.Ext2 x' j → ∀ (k : Kap x) (k' : Kap x') (e : k'.g = k.g), (∀ i g, k'.κ i g = (k.κ (Fin.cast e i) g).map j) → ∀ S : Set F.G₀, Detects k S → Detects k' S := by
  intro l _ F n x x' j hE k k' e hκ S hD z hz hell
  obtain ⟨⟨hinj, hloc, hfin, hρ, ha, -⟩, -⟩ := hE
  obtain ⟨m, b, p, -, hb, hp, -, -, r, u, -, hu⟩ := UpperTheory.V.Pa.Det.extFree j hinj hloc hfin
  obtain ⟨J, P, JC, Jep, hP, hB, Peta, PW, JW⟩ := exJP (n := n) (a := x.a) e j b p hb hp
  have hl : (l : x'.A) = 0 := by
    haveI := (UpperTheory.V.Pa.Det.zlUniq l).1 (algebraMap ℤ_[l] x'.K)
    have := congrArg (algebraMap x'.K x'.A) (CharP.cast_eq_zero x'.K l)
    rwa [map_natCast, map_zero] at this
  have he : ∀ g, epsD k' x'.A g = J (epsD k x.A g) := by
    intro g
    have := ((UpperTheory.V.Pa.Det.zlUniq l).2 (algebraMap ℤ_[l] x'.A) (j.comp (algebraMap ℤ_[l] x.A)) hl).1
    exact (congrArg DD.C (DFunLike.congr_fun this ((F.ε g : ℤ_[l]ˣ) : ℤ_[l]))).trans (JC _).symm
  have hr : ∀ g, k'.ρ1 x'.A g = (k.ρ1 x.A g).map J := by
    intro g
    have h1 : x'.ρX (DD x'.A k'.g) g = (x.ρX (DD x.A k.g) g).map J := by
      ext1 a c
      simp only [NP.ρX, hρ, Matrix.map_apply]
      exact (JC _).symm
    rw [Kap.ρ1, Kap.ρ1, Matrix.map_mul, ← h1, Matrix.map_add _ (map_add J), Jep, Matrix.map_one _ (map_zero J) (map_one J)]
    simp only [hκ]
    rfl
  have h3 : (u : x'.A) * ((u⁻¹ : (PowerSeries x'.K)ˣ) : x'.A) = 1 := u.mul_inv
  have hpow : ∀ N, (DD.C x'.t : DD x'.A k'.g) ^ (r * N) =
      J (DD.C x.t ^ N) * DD.C (((u⁻¹ : (PowerSeries x'.K)ˣ) : x'.A) ^ N) := by
    intro N
    rw [map_pow J, JC, ← map_pow, ← map_pow, ← map_mul, hu, ← mul_pow, mul_right_comm, h3, one_mul, pow_mul]
  obtain ⟨z1, z2, z3, z4⟩ := hz
  have hsm : ∀ i (c : DD x.A k.g) (Z : Matrix (Fin n) (Fin n) (DD x'.A k'.g)), (J c • Z).map (P i) = c • Z.map (P i) := by
    intro i c Z
    ext1 a c
    exact hP _ _ _
  have hzi : ∀ i, (fun g => (z g).map (P i)) ∈ TwZ k x.A := by
    intro i
    refine ⟨fun g => PW i _ (ha ▸ z1 g), fun a c N => ?_, fun g h => ?_, fun g => ?_⟩
    · have := z2 a c (r * N)
      rw [IsLocallyConstant.iff_eventually_eq] at this ⊢
      intro g
      filter_upwards [this g] with h hh
      rw [Ideal.Quotient.eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hh ⊢
      obtain ⟨w, hw⟩ := hh
      change _ = (DD.C x'.t : DD x'.A k'.g) ^ (r * N) * w at hw
      refine ⟨P i (DD.C (((u⁻¹ : (PowerSeries x'.K)ˣ) : x'.A) ^ N) * w), ?_⟩
      change P i (z h a c) - P i (z g a c) = (DD.C x.t : DD x.A k.g) ^ N * _
      rw [← map_sub, hw, hpow, mul_assoc, hP]
    · simp only
      rw [z3, Matrix.map_add _ (map_add (P i)), he, hsm, hr, hr, mapR J (P i) (hP i), mapL J (P i) (hP i)]
    · simp only
      rw [z4, Matrix.map_neg _ (map_neg (P i)), he, hsm, Matrix.transpose_map]
  have hli : ∀ i, ∀ σ ∈ S, ell k x.A σ (fun g => (z g).map (P i)) = 0 := by
    intro i σ hσ
    have h0 := hell σ hσ
    simp only [ell] at h0 ⊢
    rw [← mapR J (P i) (hP i), ← hr, ← AddMonoidHom.map_trace, Peta, h0, map_zero]
  choose s Y hY hT hs using fun i => hD _ (hzi i) (hli i)
  have hle : ∀ i, s i ≤ ∑ i, s i := fun i =>
    Finset.single_le_sum (f := s) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  set N := ∑ i, s i with hN
  let d : Fin m → x'.A := fun i => ((u⁻¹ : (PowerSeries x'.K)ˣ) : x'.A) ^ N * b i * j (x.t ^ (N - s i))
  have key : ∀ y : DD x'.A k'.g, ∑ i, d i • J (x.t ^ s i • P i y) = x'.t ^ (r * N) • y := by
    intro y
    conv_rhs => rw [hB y, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    change DD.C (d i) * J (DD.C (x.t ^ s i) * P i y) = DD.C (x'.t ^ (r * N)) * _
    have h4 : J ((DD.C x.t : DD x.A k.g) ^ N) = DD.C (j (x.t ^ (N - s i))) * J (DD.C (x.t ^ s i)) := by
      rw [← JC, ← map_mul, ← map_mul, ← pow_add, Nat.sub_add_cancel (hle i), map_pow DD.C]
    rw [map_pow DD.C x'.t, hpow, h4]
    simp only [d, map_mul]
    ring
  have hJs : ∀ (c : DD x.A k.g) (Z : Matrix (Fin n) (Fin n) (DD x.A k.g)), (c • Z).map J = J c • Z.map J := by
    intro c Z
    ext1 a c
    exact map_mul J _ _
  refine ⟨r * N, ∑ i, d i • (Y i).map J, ?_, ?_, ?_⟩
  · exact sum_mem fun i _ => Submodule.smul_mem _ _ (ha ▸ JW _ (hY i))
  · rw [Matrix.transpose_sum, Finset.smul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_rhs => rw [← hT i]
    rw [Matrix.map_neg _ (map_neg J), hJs, ← he, Matrix.transpose_smul, Matrix.transpose_map, smul_neg, smul_comm]
  · funext g
    have h5 : (x'.t ^ (r * N) • z) g = ∑ i, d i • ((x.t ^ s i • fun g => (z g).map (P i)) g).map J := by
      ext1 a c
      rw [Matrix.sum_apply]
      exact (key _).symm
    rw [h5, Finset.mul_sum, Finset.sum_mul, Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hs i]
    simp only
    rw [Matrix.map_sub _ (map_sub J), hJs, Matrix.map_mul, Matrix.map_mul, ← he, ← hr, ← hr, smul_sub,
      Matrix.mul_smul, Matrix.smul_mul, smul_comm]
