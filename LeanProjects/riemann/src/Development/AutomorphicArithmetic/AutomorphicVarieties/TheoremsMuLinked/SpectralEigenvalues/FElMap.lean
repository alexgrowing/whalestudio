import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdinaryHeckeAlgebraIntegral
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.SpectralEigenvalues.ImportsTer
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.SpectralEigenvalues.LamW
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.SpectralEigenvalues.ImportsFurther
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.SpectralEigenvalues.BetaLam
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.SpectralEigenvalues.BetaSurj
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.SpectralEigenvalues.GenAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.SpectralEigenvalues.RepSingle
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap
open IsLocalRing Matrix Filter UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.V.AlgebraTools UpperTheory.V.Th
open scoped TensorProduct

private theorem fEl_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {q n : ℕ} (Nq : Fin q → ℕ) (u : Fin q → Fin n → R) :
    f (fEl Nq u) = fEl Nq fun j i => f (u j i) := by
  simp [fEl]

private theorem chi_rep {n : ℕ} {A G : Type} [CommRing A] [Group G] (ρ : G →* Matrix (Fin n) (Fin n) A) (g : G) :
    (GDet.ofRep ρ).chi (MonoidAlgebra.single g 1) = (ρ g).charpoly := by
  change (GDet.repAlg ρ (Polynomial A) _).det = _
  rw [map_sub, MonoidAlgebra.mapRingHom_single, Matrix.charpoly]
  congr 1
  ext i j : 2
  by_cases h : i = j <;> simp [GDet.repAlg, Matrix.charmatrix, h, Matrix.one_apply, Matrix.diagonal_apply]

private theorem g_dvd {O : Type} [CommRing O] {q n : ℕ} (Nq : Fin q → ℕ) (α : Fin q → Fin n → O) :
    (∏ j, ∏ i, ∏ k ∈ Finset.univ.erase i, (α j i - α j k)) ∣ fEl Nq α :=
  Finset.prod_dvd_prod_of_dvd _ _ fun _ _ => Finset.prod_dvd_prod_of_dvd _ _ fun _ _ =>
    Finset.prod_dvd_prod_of_dvd _ _ fun _ _ => dvd_mul_right _ _

private theorem e_dvd {O : Type} [CommRing O] {q n : ℕ} (α : Fin q → Fin n → O) (j : Fin q) (i : Fin n) :
    (∏ k ∈ Finset.univ.erase i, (α j i - α j k)) ∣ ∏ j, ∏ i, ∏ k ∈ Finset.univ.erase i, (α j i - α j k) :=
  (Finset.dvd_prod_of_mem (fun i => ∏ k ∈ Finset.univ.erase i, (α j i - α j k)) (Finset.mem_univ i)).trans
    (Finset.dvd_prod_of_mem (fun j => ∏ i, ∏ k ∈ Finset.univ.erase i, (α j i - α j k)) (Finset.mem_univ j))

private theorem num_dvd {O : Type} [CommRing O] (a g F e z c : O) (E : ℕ) (h1 : g ∣ F) (h2 : e ∣ F)
    (h : a ^ 2 * z * F ^ (3 * E + 6) ∣ c) : (a * g * F * F ^ E) ^ 2 * (F * z) * e ^ (E + 1) ∣ c := by
  refine Dvd.dvd.trans ?_ h
  obtain ⟨g', hg⟩ := h1
  obtain ⟨e', he⟩ := h2
  refine ⟨g' ^ 2 * e' ^ (E + 1), ?_⟩
  have : F ^ (3 * E + 6) = (g * g') ^ 2 * (F * F ^ E) ^ 2 * F * (e * e') ^ (E + 1) := by
    rw [← hg, ← he]; ring
  rw [this]; ring

theorem UpperTheory.V.Th.Sp.one :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 G : Glob l L) (h : G.Hom G0) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (b : TWBase u J Empty D) (q N : ℕ) (A : OpMod b h q N) (y : Pt G0.frame O n) (x : B →ₐ[O] O) (Nq : Fin q → ℕ) (ph ta : Fin q → G.G₀) (E : ℕ) (α : Fin q → Fin n → O) (t₀ : B) (lam : b.M →+ O) (m₀ : b.M) (m : ℕ) (c : O), 1 ≤ n → GenBy O (pairVals u) → u.Maps x.toRingHom (GDet.ofRep (mat y.ρ)) y.ψ → (∀ a : B, x a = 0 → ∀ w : b.M, (t₀ * a) • w ∈ wtSub b x) → (∀ (a : B) w, lam (a • w) = x a * lam w) → (∀ j, h.p₀ (ta j) = 1) → (∀ j, (mat y.ρ (h.p₀ (ph j))).charpoly = ∏ k, (Polynomial.X - Polynomial.C (α j k))) → OpRelX A Nq ph ta E → m ≤ N → x t₀ ^ 2 * lam m₀ * fEl Nq α ^ (3 * E + 6) ∣ c → ∀ a : Fin D ⊕ Fin q × Fin n, ∃ δ : A.R →ₗ[O] Om O m, IsDer (x.comp A.β) δ ∧ (∀ k, δ (algebraMap (abelian₂ O Empty D) A.R (MvPowerSeries.X (.inr k))) = if a = .inl k then algebraMap O _ c else 0) ∧ ∀ j i, δ (A.p.D.tr (twoPowerModulus E (ph j) (ta j) (fun k => algebraMap O A.R (α j k)) i 0)) = if a = .inr (j, i) then algebraMap O _ c else 0 := by
  intro l _ L G0 G h n O _ _ _ _ _ r B _ _ _ u J D b q N A y x Nq ph ta E α t₀ lam m₀ m c hn hgen hmap hEt hlam hta hα hA hN hc a
  have hs := Sp.betaSurj l L G0 G h n O r B u J D b q N A hgen
  have hβ := Sp.betaLam l L G0 G h n O r B u J D b q N A
  obtain ⟨t₁, rfl⟩ := hs t₀
  have hP : ∀ j, (u.D.chi (MonoidAlgebra.single (h.p₀ (ph j)) 1)).map (x : B →+* O) =
      ∏ i, (Polynomial.X - Polynomial.C (α j i)) := fun j => by
    have h1 := ((UpperTheory.V.CA.d_gmap u.D).2.2.1 x.toRingHom (MonoidAlgebra.single (h.p₀ (ph j)) 1)).1
    rw [MonoidAlgebra.mapRingHom_single, map_one, hmap.1, chi_rep, hα j] at h1
    exact h1.symm
  obtain ⟨lw, v₀, hlw, hv₀⟩ := Sp.lamW O A.R B b.M A.Mw q n A.β x _ A.actw _ α lam m₀ hA.two hP hlam
  obtain ⟨htr, hker⟩ := Sp.trans A.R A.M1 A.Mw q n A.act1 A.actw A.tr A.tr_surj A.tr_ker A.tr_u
  obtain ⟨v, rfl⟩ := A.tr_surj v₀
  let xU : PU A.R q n →+* O := MvPolynomial.eval₂Hom ((x.comp A.β : A.R →ₐ[O] O) : A.R →+* O) fun p => α p.1 p.2
  let π : PUY A.R q n →ₐ[A.R] PU A.R q n := MvPolynomial.aeval (Sum.elim MvPolynomial.X 0)
  let xT : PUY A.R q n →ₐ[O] O :=
    { xU.comp (π : PUY A.R q n →+* PU A.R q n) with
      commutes' := fun o => by
        change xU (π (MvPolynomial.C (algebraMap O A.R o))) = o
        simp [xU, π] }
  have hxT : ∀ τ, xT τ = xU (π τ) := fun _ => rfl
  have hC : ∀ s, xT (MvPolynomial.C s) = x (A.β s) := fun s => by simp [hxT, xU, π]
  have hU : ∀ j k, xT (uV A.R j k) = α j k := fun j k => by simp [hxT, xU, π]
  have hY : ∀ j k, xT (yV A.R j k) = 0 := fun j k => by simp [hxT, xU, π]
  let I : Ideal A.R := (RingHom.ker (x.comp b.lam)).map (algebraMap (abelian₂ O Empty D) A.R)
  have hI : ∀ w, w ∈ wtSub b x → w ∈ (I.map A.β • ⊤ : Submodule B b.M) := fun w hw => by
    refine Submodule.smul_induction_on hw (fun s hs w _ => ?_) fun _ _ => add_mem
    rw [b.smul_lam, ← hβ]
    exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hs)) trivial
  have hkill := Sp.kill O A.R B b.M A.Mw q n A.β x _ A.actw _ α I t₁ hs hA.two hP fun a ha w => hI _ (hEt a ha w)
  let t : PUY A.R q n := MvPolynomial.C t₁ * (∏ j, ∏ i, ∏ k ∈ Finset.univ.erase i,
    (uV A.R j i - MvPolynomial.C (algebraMap O A.R (α j k)))) * fEl Nq (uV A.R) * fEl Nq (uV A.R) ^ E
  have hF : xT (fEl Nq (uV A.R)) = fEl Nq α := by
    have := fEl_map (xT : PUY A.R q n →+* O) Nq (uV A.R)
    simpa [hU] using this
  have hxt : xT t = x (A.β t₁) * (∏ j, ∏ i, ∏ k ∈ Finset.univ.erase i, (α j i - α j k)) * fEl Nq α * fEl Nq α ^ E := by
    simp only [t, map_mul, map_pow, map_prod, map_sub, hC, hU, hF, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]
  have hv : lw (A.tr v) = fEl Nq α * lam m₀ := by
    rw [hv₀]
    congr 1
    have := fEl_map xU Nq fun j i => MvPolynomial.X (j, i)
    simpa [xU] using this
  obtain ⟨del, hd, h1, h2, h3⟩ := Sp.derOp l L G0 G h n O r B u J D b q N A xT (lw.comp A.tr.toAddMonoidHom) t v I m hN hY
    (fun τ w => by
      change lw (A.tr (A.act1 τ w)) = xT τ * lw (A.tr w)
      rw [htr, hlw]; rfl)
    (Ideal.span_le.2 (by
      rintro _ ⟨s, hs, rfl⟩
      exact Ideal.subset_span ⟨s, rfl, by rw [hC, hβ]; exact hs⟩))
    (fun s hs w => hker I _ (by
      have hπ : π (fEl Nq (uV A.R)) = fEl Nq fun j i => MvPolynomial.X (j, i) := by
        have := fEl_map (π : PUY A.R q n →+* PU A.R q n) Nq (uV A.R)
        simpa [π] using this
      have e : π (t * s) = MvPolynomial.C t₁ * (∏ j, ∏ i, ∏ k ∈ Finset.univ.erase i,
          (MvPolynomial.X (j, i) - MvPolynomial.C (algebraMap O A.R (α j k)))) * (fEl Nq fun j i => MvPolynomial.X (j, i)) *
          π (fEl Nq (uV A.R) ^ E * s) := by
        simp only [t, map_mul, map_prod, map_sub, hπ, mul_assoc]
        simp [π]
      rw [htr]
      change A.actw (π (t * s)) _ ∈ _
      rw [e]
      refine hkill _ ?_ _
      change xT _ = 0
      rw [map_mul, hs, mul_zero])) a
  have hv' : (lw.comp A.tr.toAddMonoidHom) v = fEl Nq α * lam m₀ := hv
  rw [hv'] at h1 h2
  have hq : ∀ j i, del (MvPolynomial.C (A.p.D.tr (twoPowerModulus E (ph j) (ta j) (fun k => algebraMap O A.R (α j k)) i 0))) =
      (∏ k ∈ Finset.univ.erase i, (α j i - α j k)) ^ (E + 1) • del (yV A.R j i) := fun j i => by
    obtain ⟨k1, k2⟩ := Sp.q2op l L G0 G h n O r B u J D b q N A y x (ph j) (ta j) (α j) E j i xT _ del hn hmap (hta j) (hα j)
      hC (hU j) (hY j i) hd
    have := h3 _ k1 (by
      simp only [t]
      rw [mul_assoc, map_mul, hA.rel2, mul_zero])
    rw [this] at k2
    exact sub_eq_zero.1 k2.symm
  let δ₀ : A.R →ₗ[O] Om O m := del ∘ₗ (IsScalarTower.toAlgHom O A.R (PUY A.R q n)).toLinearMap
  have hδ : ∀ s, δ₀ s = del (MvPolynomial.C s) := fun _ => rfl
  have hder : ∀ e : O, IsDer (x.comp A.β) (e • δ₀) := fun e s s' => by
    simp only [LinearMap.smul_apply, hδ, map_mul, hd _ _, hC, AlgHom.comp_apply, smul_add, smul_comm e]
  have hnum := fun j i => num_dvd _ _ _ _ _ c E (g_dvd Nq α) ((e_dvd α j i).trans (g_dvd Nq α)) hc
  have hn0 := num_dvd _ _ _ 1 _ c E (g_dvd Nq α) (one_dvd _) hc
  rw [← hxt] at hnum hn0
  rcases a with k | ⟨j, i⟩
  · obtain ⟨e, he⟩ := hn0
    refine ⟨e • δ₀, hder e, fun k' => ?_, fun j i => ?_⟩
    · rw [LinearMap.smul_apply, hδ, h1]
      split_ifs
      · rw [he, Algebra.smul_def, ← map_mul]; congr 1; ring
      · simp
    · rw [LinearMap.smul_apply, hδ, hq, h2]; simp
  · obtain ⟨e, he⟩ := hnum j i
    refine ⟨e • δ₀, hder e, fun k' => ?_, fun j' i' => ?_⟩
    · rw [LinearMap.smul_apply, hδ, h1]; simp
    · rw [LinearMap.smul_apply, hδ, hq, h2]
      split_ifs with hh
      · obtain ⟨rfl, rfl⟩ : j = j' ∧ i = i' := by simpa using hh
        rw [he, Algebra.smul_def, Algebra.smul_def, ← map_mul, ← map_mul]; congr 1; ring
      · simp
