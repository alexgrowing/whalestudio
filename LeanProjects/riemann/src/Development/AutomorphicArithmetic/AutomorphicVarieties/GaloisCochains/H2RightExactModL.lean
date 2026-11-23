import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.GLinkQuot
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.Fr UpperTheory.V.GC

section

variable {k G M : Type} [CommRing k] [Group G] [AddCommGroup M] [Module k M]

private theorem dn_two (ρ : Representation k G M) (b : (Fin 2 → G) → M) (x y z : G) :
    dn ρ 2 b ![x, y, z] = ρ x (b ![y, z]) - b ![x * y, z] + b ![x, y * z] - b ![x, y] := by
  have e0 : (fun i : Fin 2 => (![x, y, z] : Fin 3 → G) i.succ) = ![y, z] := by
    funext i; fin_cases i <;> rfl
  have e1 : Fin.contractNth 0 (· * ·) (![x, y, z] : Fin 3 → G) = ![x * y, z] := by
    funext i; fin_cases i <;> rfl
  have e2 : Fin.contractNth 1 (· * ·) (![x, y, z] : Fin 3 → G) = ![x, y * z] := by
    funext i; fin_cases i <;> rfl
  have e3 : Fin.contractNth 2 (· * ·) (![x, y, z] : Fin 3 → G) = ![x, y] := by
    funext i; fin_cases i <;> rfl
  change ρ _ (b _) + Finset.univ.sum (fun j : Fin 3 =>
      (-1 : k) ^ ((j : ℕ) + 1) • b (Fin.contractNth j (· * ·) ![x, y, z])) = _
  rw [Fin.sum_univ_three, e0, e1, e2, e3]
  have p3 : (-1 : k) ^ 3 = -1 := by ring
  simp [p3]
  abel

private theorem dn_three (ρ : Representation k G M) (b : (Fin 3 → G) → M) (x y z w : G) :
    dn ρ 3 b ![x, y, z, w] = ρ x (b ![y, z, w]) - b ![x * y, z, w] + b ![x, y * z, w]
      - b ![x, y, z * w] + b ![x, y, z] := by
  have e0 : (fun i : Fin 3 => (![x, y, z, w] : Fin 4 → G) i.succ) = ![y, z, w] := by
    funext i; fin_cases i <;> rfl
  have e1 : Fin.contractNth 0 (· * ·) (![x, y, z, w] : Fin 4 → G) = ![x * y, z, w] := by
    funext i; fin_cases i <;> rfl
  have e2 : Fin.contractNth 1 (· * ·) (![x, y, z, w] : Fin 4 → G) = ![x, y * z, w] := by
    funext i; fin_cases i <;> rfl
  have e3 : Fin.contractNth 2 (· * ·) (![x, y, z, w] : Fin 4 → G) = ![x, y, z * w] := by
    funext i; fin_cases i <;> rfl
  have e4 : Fin.contractNth 3 (· * ·) (![x, y, z, w] : Fin 4 → G) = ![x, y, z] := by
    funext i; fin_cases i <;> rfl
  change ρ _ (b _) + Finset.univ.sum (fun j : Fin 4 =>
      (-1 : k) ^ ((j : ℕ) + 1) • b (Fin.contractNth j (· * ·) ![x, y, z, w])) = _
  rw [Fin.sum_univ_four, e0, e1, e2, e3, e4]
  have p3 : (-1 : k) ^ 3 = -1 := by ring
  have p4 : (-1 : k) ^ 4 = 1 := by ring
  simp [p3, p4]
  abel

private theorem H2_map_surjective_of_H3_subsingleton [TopologicalSpace G] [ContinuousMul G] [TopologicalSpace M] [DiscreteTopology M]
    {Q N : Type} [AddCommGroup Q] [Module k Q] [TopologicalSpace Q] [DiscreteTopology Q]
    [AddCommGroup N] [Module k N] [TopologicalSpace N] [DiscreteTopology N]
    (ρ : Representation k G M) (σ : Representation k G Q) (τ : Representation k G N) (hc : ContAction ρ)
    (q : M →ₗ[k] Q) (hq : ∀ s m, q (ρ s m) = σ s (q m)) (hs : Function.Surjective q)
    (i : N →ₗ[k] M) (hi : ∀ s m, i (τ s m) = ρ s (i m)) (hinj : Function.Injective i)
    (hex : ∀ m, q m = 0 ↔ ∃ n, i n = m) (h3 : Subsingleton (Hn τ 3)) :
    Function.Surjective (mapH2 ρ σ q continuous_of_discreteTopology hq) := by
  classical
  intro cl
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ cl
  obtain ⟨sec, hsec⟩ := hs.hasRightInverse
  let Φ : G × G → M := fun p => sec (f.1 p)
  have hΦ : Continuous Φ := continuous_of_discreteTopology.comp f.2.1
  have hqΦ : ∀ p, q (Φ p) = f.1 p := fun p => hsec _
  let c : (Fin 3 → G) → M := fun g =>
    ρ (g 0) (Φ (g 1, g 2)) - Φ (g 0 * g 1, g 2) + Φ (g 0, g 1 * g 2) - Φ (g 0, g 1)
  have hcc : Continuous c := by
    have h0 : Continuous fun g : Fin 3 → G => ρ (g 0) (Φ (g 1, g 2)) :=
      hc.comp (f := fun g : Fin 3 → G => (g 0, Φ (g 1, g 2))) (by fun_prop)
    exact ((h0.sub (by fun_prop)).add (by fun_prop)).sub (by fun_prop)
  have hqc : ∀ g, q (c g) = 0 := fun g => by
    simp only [c, map_sub, map_add, hq, hqΦ]
    exact f.2.2 _ _ _
  let r : M → N := Function.invFun i
  have hr : ∀ g, i (r (c g)) = c g := fun g => Function.invFun_eq ((hex _).1 (hqc g))
  obtain ⟨b, hb, hbc⟩ := (GlobalTheory.Published.subsingleton_Hn_succ_iff τ 2).1 h3 (fun g => r (c g))
    ((continuous_of_discreteTopology (f := r)).comp hcc) (by
      funext g
      obtain ⟨x, y, z, w, rfl⟩ : ∃ x y z w, g = ![x, y, z, w] :=
        ⟨g 0, g 1, g 2, g 3, by funext j; fin_cases j <;> rfl⟩
      apply hinj
      rw [dn_three]
      simp only [map_add, map_sub, hi, hr, Pi.zero_apply, map_zero]
      simp [c, mul_assoc]
      abel)
  have hb' : Continuous fun p : G × G => i (b ![p.1, p.2]) :=
    continuous_of_discreteTopology.comp (hb.comp (by fun_prop))
  refine ⟨Submodule.Quotient.mk ⟨fun p => Φ p - i (b ![p.1, p.2]), hΦ.sub hb', fun x y z => ?_⟩, ?_⟩
  · have e := congrArg i (congrFun hbc ![x, y, z])
    rw [dn_two] at e
    simp only [map_add, map_sub, hi, hr] at e
    simp only [c, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at e
    simp only [map_sub]
    rw [← sub_eq_zero.2 e.symm]
    abel
  · change Submodule.Quotient.mk _ = _
    congr 1
    apply Subtype.ext
    funext p
    change q (Φ p - i (b ![p.1, p.2])) = _
    rw [map_sub, hqΦ, (hex _).2 ⟨_, rfl⟩, sub_zero]

end

theorem UpperTheory.V.GC.local_second_cohomology_surjective_at_place :
    LocalFiniteness → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), IsPlaceOver A v → ∀ (k : Type) [Field k] [Finite k] [CharP k l] (M : Type) [AddCommGroup M] [Module k M] [Module.Finite k M] [TopologicalSpace M] [DiscreteTopology M] (Q : Type) [AddCommGroup Q] [Module k Q] [TopologicalSpace Q] [DiscreteTopology Q]
    (ρ : Representation k (Dec (F := F) A) M) (σ : Representation k (Dec (F := F) A) Q), ContAction ρ → ∀ (q : M →ₗ[k] Q) (hq : ∀ s m, q (ρ s m) = σ s (q m)), Function.Surjective q →
    Function.Surjective (mapH2 ρ σ q continuous_of_discreteTopology hq) := by
  intro hLF F Ω _ _ _ _ _ l _ v A hA k _ _ _ M _ _ _ _ _ Q _ _ _ _ ρ σ hc q hq hs
  haveI : Finite M := Module.finite_of_finite k
  have hst : ∀ g, LinearMap.ker q ≤ (LinearMap.ker q).comap (ρ g) := fun g m hm => by
    rw [Submodule.mem_comap, LinearMap.mem_ker, hq, LinearMap.mem_ker.1 hm, map_zero]
  let τ := ρ.subrepresentation (LinearMap.ker q) hst
  have hτ : ContAction τ :=
    Continuous.subtype_mk (hc.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))) _
  refine H2_map_surjective_of_H3_subsingleton ρ σ τ hc q hq hs (LinearMap.ker q).subtype (fun _ _ => rfl) Subtype.val_injective
    (fun m => ⟨fun h => ⟨⟨m, h⟩, rfl⟩, by rintro ⟨n, rfl⟩; exact n.2⟩) ?_
  refine (GlobalTheory.Published.cohDimTwoLocal_of_localFiniteness hLF).of_nsmul l 1 (fun m => ?_) τ hA hτ 3 le_rfl
  rw [pow_one, ← Nat.cast_smul_eq_nsmul k, CharP.cast_eq_zero, zero_smul]
