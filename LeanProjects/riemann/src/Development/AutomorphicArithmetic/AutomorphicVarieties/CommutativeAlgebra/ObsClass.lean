import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedTwoCoboundaries
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.HhGroup
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.HomogSpan
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.HhSection
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.LocGradedTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.KerCoef
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ObsCocycle
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ObsCorrect

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem ac_mul {S A ι : Type} [TopologicalSpace S] [CommRing A] [Fintype ι] (I : Ideal A)
    {M N : S → Matrix ι ι A} (hM : ∀ a b, AdicCont I fun s => M s a b) (hN : ∀ a b, AdicCont I fun s => N s a b) :
    ∀ a b, AdicCont I fun s => (M s * N s) a b := by
  intro a b n
  classical
  simp only [Matrix.mul_apply, map_sum, map_mul]
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact IsLocallyConstant.const _
  | insert c t hc ih =>
    simp only [Finset.sum_insert hc]
    exact ((hM a c n).mul (hN c b n)).add ih

private theorem ac_map {O S R R' : Type} [CommRing O] [IsLocalRing O] [TopologicalSpace S] [CommRing R] [Algebra O R]
    [IsCO O R] [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R') {x : S → R}
    (hx : AdicCont (maximalIdeal R) x) : AdicCont (maximalIdeal R') fun s => f (x s) := by
  intro N
  have hle : maximalIdeal R ^ N ≤ (maximalIdeal R' ^ N).comap (f : R →+* R') := by
    refine le_trans (Ideal.pow_right_mono (fun y hy => ?_) N) (Ideal.le_comap_pow _ N)
    show f y ∈ maximalIdeal R'
    rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]
    exact hy
  exact (hx N).comp (Ideal.quotientMap _ (f : R →+* R') hle)

private theorem hmul {O ι X R : Type} [CommRing O] [Fintype ι] [AddCommGroup X] [CommRing R] [Algebra O R]
    (P : X → Submodule O R) (hP : ∀ i j x y, x ∈ P i → y ∈ P j → x * y ∈ P (i + j)) (w : ι → X)
    {A B : Matrix ι ι R} (hA : ∀ a b, A a b ∈ P (w a - w b))
    (hB : ∀ a b, B a b ∈ P (w a - w b)) : ∀ a b, (A * B) a b ∈ P (w a - w b) := by
  intro a b
  rw [Matrix.mul_apply]
  refine Submodule.sum_mem _ fun c _ => ?_
  have := hP _ _ _ _ (hA a c) (hB c b)
  rwa [sub_add_sub_cancel] at this

private theorem hconst {O ι X R : Type} [CommRing O] [AddCommGroup X] [CommRing R] [Algebra O R]
    (P : X → Submodule O R) (hP : (1 : R) ∈ P 0) (w : ι → X) {M : Matrix ι ι O}
    (hM : ∀ a b, w a ≠ w b → M a b = 0) : ∀ a b, (M.map (algebraMap O R)) a b ∈ P (w a - w b) := by
  intro a b
  rw [Matrix.map_apply]
  by_cases h : w a = w b
  · rw [h, sub_self, Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _ hP
  · rw [hM a b h, map_zero]
    exact zero_mem _

private theorem norm_comp {O : Type} [CommRing O] {ι X : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup X]
    {w : ι → X} {Φ : FormData O w} {R : Type} [CommRing R] [Algebra O R] {Γ H : Type} [Group Γ] [Group H]
    {ρ : Γ →* Matrix ι ι R} (h : Φ.Normalises ρ) (φ : H →* Γ) : Φ.Normalises (ρ.comp φ) := by
  obtain ⟨h1, ⟨π, h2⟩, h3⟩ := h
  exact ⟨fun g => h1 (φ g), ⟨π.comp φ, fun g => h2 (φ g)⟩, fun g => h3 (φ g)⟩

private theorem ex_mu {O A : Type} [CommRing O] [IsLocalRing O] [CommRing A] [Algebra O A] [IsCO O A] (η : A)
    (hη : ∀ x ∈ maximalIdeal A, x * η = 0) :
    ∃ μ : ResidueField O →+ A, (∀ a : O, μ (residue O a) = a • η) ∧ ∀ (a : A) c, μ (res O A a * c) = a * μ c := by
  have k : ∀ a b : O, residue O a = residue O b → a • η = b • η := fun a b h => by
    rw [← sub_eq_zero, ← sub_smul, Algebra.smul_def]
    refine hη _ ?_
    rw [← res_eq_zero_iff O, AlgHom.commutes, ResidueField.algebraMap_eq, map_sub, h, sub_self]
  choose s hs using residue_surjective (R := O)
  have k2 : ∀ a : O, s (residue O a) • η = a • η := fun a => k _ _ (hs _)
  refine ⟨AddMonoidHom.mk' (fun c => s c • η) fun c d => ?_, k2, fun a c => ?_⟩
  · rw [← add_smul]
    exact k _ _ (by rw [map_add, hs, hs, hs])
  · obtain ⟨b, hb⟩ := IsCO.res_surj (O := O) a
    have e : res O A a = residue O b := by
      have := (res_eq_zero_iff O A _).2 hb
      rwa [map_sub, AlgHom.commutes, sub_eq_zero] at this
    have e2 : a * η = b • η := by
      have := hη _ hb
      rwa [sub_mul, sub_eq_zero, ← Algebra.smul_def] at this
    show s _ • η = a * (s c • η)
    rw [mul_smul_comm, e2, smul_smul]
    exact k _ _ (by rw [map_mul, hs, hs, e, mul_comm])

private theorem mmap {O R S ι : Type} [CommRing O] [CommRing R] [CommRing S] [Algebra O R] [Algebra O S]
    [Fintype ι] (f : R →ₐ[O] S) (A B : Matrix ι ι R) : (A * B).map f = A.map f * B.map f :=
  Matrix.map_mul (f := (f : R →+* S))

private theorem cmap {O R S ι : Type} [CommRing O] [CommRing R] [CommRing S] [Algebra O R] [Algebra O S]
    (f : R →ₐ[O] S) (A : Matrix ι ι O) : (A.map (algebraMap O R)).map f = A.map (algebraMap O S) := by
  ext a b
  simp

theorem UpperTheory.V.Alg.obs_class :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (ι X : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (w : ι → X) (Φ : FormData O w), IsUnit (2 : O) → ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (rbar : Γ →* Matrix ι ι (ResidueField O)) (r0 : Lift O rbar O) (hbar : Φ.Normalises rbar), Φ.Normalises r0.hom → ∀ (F : Frame Γ) (L : ∀ q, Cond O (rbar.comp (F.ψ q))), (∀ q, ∀ n ∈ F.N q, rbar (F.ψ q n) = 1) → (∀ q, Φ.IsLocCond (r0.hom.comp (F.ψ q)) (F.N q) (L q)) → (∀ q, L q O (r0.comap (F.ψ q) (F.hψ q))) →
      ∀ (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (ρ : ∀ v, Lift O (rbar.comp (F.φ v)) B), (∀ v, Φ.InH (r0.hom.comp (F.φ v)) B (ρ v)) → ∀ (A : Type) [CommRing A] [Algebra O A] [IsCO O A] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (p : A →ₐ[O] R), Function.Surjective p → maximalIdeal A * RingHom.ker p = ⊥ → ∀ (W : WPres O X A), (∀ s, W.z s ∈ maximalIdeal A) →
      ∀ (κ : Type) [Fintype κ] (ε : κ → A) (wf : κ → X), (∀ u, ε u ∈ W.part (wf u)) → RingHom.ker p = Ideal.span (Set.range ε) → (∀ c : κ → O, ∑ u, c u • ε u = 0 → ∀ u, c u ∈ maximalIdeal O) →
      ∀ (i : B →ₐ[O] A) (r : Lift O rbar R) (α : F.T → Matrix ι ι R), IsFramed Φ r0.hom F L ρ (p.comp i) r α →
      (∀ v s a b, i ((ρ v).hom s a b) ∈ W.part (w a - w b)) → (∀ s a b, r.hom s a b ∈ (W.part (w a - w b)).map p.toLinearMap) → (∀ v a b, α v a b ∈ (W.part (w a - w b)).map p.toLinearMap) →
      ∃ o : ∀ j, {u // wf u = j} → F.Ob (FormData.adRep hbar j), ∀ (j : X) [Fintype {u // wf u = j}] (c : {u // wf u = j} → O), ∑ u, residue O (c u) • o j u = 0 →
        ∀ (A' : Type) [CommRing A'] [Algebra O A'] [IsCO O A'] (p' : A →ₐ[O] A') (p'' : A' →ₐ[O] R) (η : A'), Function.Surjective p' → p''.comp p' = p → (∀ x ∈ maximalIdeal A', x * η = 0) → p'' η = 0 →
          (∀ u : {u // wf u = j}, p' (ε u) = c u • η) → (∀ u, wf u ≠ j → p' (ε u) = 0) →
          ∃ (r' : Lift O rbar A') (α' : F.T → Matrix ι ι A'), IsFramed Φ r0.hom F L ρ (p'.comp i) r' α' ∧ r'.map p'' = r ∧ ∀ v, (α' v).map p'' = α v := by
  intro O _ _ _ _ ι X _ _ _ _ _ w Φ h2 Γ _ _ _ rbar r0 hbar h0 F L hN hL hL0 B _ _ _ ρ hρ A _ _ _ R _ _ _ p hp hs W hz
    κ _ ε wf hε hK hind i r α hfr hw1 hw2 hw3
  classical
  obtain ⟨hr, hrL, hα, hα0, hE⟩ := hfr
  have P1 : ∀ i j x y, x ∈ W.part i → y ∈ W.part j → x * y ∈ W.part (i + j) := fun _ _ _ _ hx hy =>
    SetLike.GradedMul.mul_mem hx hy
  have P0 : (1 : A) ∈ W.part 0 := SetLike.GradedOne.one_mem
  have Q1 : ∀ i j x y, x ∈ (W.part i).map p.toLinearMap → y ∈ (W.part j).map p.toLinearMap →
      x * y ∈ (W.part (i + j)).map p.toLinearMap := by
    rintro _ _ _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x * y, P1 _ _ _ _ hx hy, map_mul p x y⟩
  have Q0 : (1 : R) ∈ (W.part 0).map p.toLinearMap := ⟨1, P0, map_one p⟩
  have c0 : ∀ (S : Type) [CommRing S] [Algebra O S] [IsCO O S] (a b : ι),
      AdicCont (maximalIdeal S) fun s => ((r0.hom s).map (algebraMap O S)) a b := fun S _ _ _ a b =>
    ac_map (Algebra.ofId O S) (r0.cont a b)
  have inv0 : ∀ (S : Type) [CommRing S] [Algebra O S] (s t : Γ), s * t = 1 →
      (r0.hom s).map (algebraMap O S) * (r0.hom t).map (algebraMap O S) = 1 := fun S _ _ s t h => by
    rw [← Matrix.map_mul, ← map_mul, h, map_one, Matrix.map_one _ (map_zero _) (map_one _)]
  obtain ⟨ht, ht1, ht2, ht3, ht4⟩ := hh_section O ι X w Φ h2 A R p hp hs W hz Γ
    (fun s => r.hom s * (r0.hom s⁻¹).map (algebraMap O R)) hr
    (ac_mul _ r.cont fun a b n => (c0 R a b n).comp_continuous continuous_inv)
    (fun s => hmul _ Q1 w (hw2 s) (hconst (fun i => (W.part i).map p.toLinearMap) Q0 w (h0.2.2 _)))
  obtain ⟨rt, r1, r2, r3, r4⟩ : ∃ rt : Γ → Matrix ι ι A, (∀ s, Φ.HH (rt s * (r0.hom s⁻¹).map (algebraMap O A))) ∧
      (∀ a b, AdicCont (maximalIdeal A) fun s => rt s a b) ∧ (∀ s a b, rt s a b ∈ W.part (w a - w b)) ∧
      ∀ s, (rt s).map p = r.hom s := by
    refine ⟨fun s => ht s * (r0.hom s).map (algebraMap O A), fun s => ?_, ac_mul _ ht2 (c0 A),
      fun s => hmul _ P1 w (ht3 s) (hconst _ P0 w (h0.2.2 _)), fun s => ?_⟩
    · rw [mul_assoc, inv0 A _ _ (mul_inv_cancel s), mul_one]
      exact ht1 s
    · rw [mmap, ht4, cmap, mul_assoc, inv0 R _ _ (inv_mul_cancel s), mul_one]
  obtain ⟨αt, a1, a2, a3, a4⟩ : ∃ αt : F.T → Matrix ι ι A, (∀ v, Φ.HH (αt v)) ∧
      (∀ v a b, αt v a b ∈ W.part (w a - w b)) ∧ (∀ v, (αt v).map p = α v) ∧ αt F.v0 = 1 := by
    letI : TopologicalSpace F.T := ⊥
    haveI : DiscreteTopology F.T := ⟨rfl⟩
    obtain ⟨β, b1, -, b3, b4⟩ := hh_section O ι X w Φ h2 A R p hp hs W hz F.T α hα
      (fun a b n => IsLocallyConstant.of_discrete _) hw3
    refine ⟨fun v => if v = F.v0 then 1 else β v, fun v => ?_, fun v => ?_, fun v => ?_, if_pos rfl⟩
    · beta_reduce
      split_ifs
      · exact (hh_group O ι X w Φ A).1
      · exact b1 v
    · beta_reduce
      split_ifs
      · have := hconst (R := A) _ P0 w (M := 1) fun a b h => Matrix.one_apply_ne fun e => h (by rw [e])
        rwa [Matrix.map_one _ (map_zero _) (map_one _)] at this
      · exact b3 v
    · beta_reduce
      split_ifs with h
      · rw [h, hα0, Matrix.map_one _ (map_zero _) (map_one _)]
      · exact b4 v
  have hhom : IsHomog O W.wt (RingHom.ker (p.comp W.π)) := by
    have := (homog_span O A X W κ (fun u => ⟨ε u, W.part_le_A (hε u)⟩) wf hε).1
    rw [← hK] at this
    exact this
  choose rq q1 q2 q3 q4 using fun q => loc_graded_top O ι X w Φ h2 (F.Gq q) (rbar.comp (F.ψ q))
    (r0.comap (F.ψ q) (F.hψ q)) (norm_comp hbar _) (norm_comp h0 _) (F.N q) (L q) (hL q) A R p hp hs W hz hhom
    (r.comap (F.ψ q) (F.hψ q)) (fun s => by simpa [Lift.comap] using hr (F.ψ q s)) (hrL q) (fun s => hw2 _)
  obtain ⟨co, k1, k2, k3, k4⟩ := ker_coef O X A (RingHom.ker p) hs W κ ε wf hε hK hind
  have inH : ∀ (S S' : Type) [CommRing S] [Algebra O S] [IsCO O S] [CommRing S'] [Algebra O S'] [IsCO O S']
      (f : S →ₐ[O] S') (M : Matrix ι ι S) (N : Matrix ι ι O), Φ.HH (M * N.map (algebraMap O S)) →
      Φ.HH (M.map f * N.map (algebraMap O S')) := fun S S' _ _ _ _ _ _ f M N h => by
    have := (hh_group O ι X w Φ S).2.2.2.1 S' f _ h
    rwa [mmap, cmap] at this
  have d1 : ∀ s t, (rt s * rt t).map p = (rt (s * t)).map p := fun s t => by
    rw [mmap, r4, r4, r4, map_mul]
  have d2 : ∀ v s, (rt (F.φ v s) * αt v).map p = (αt v * ((ρ v).map i).hom s).map p := fun v s => by
    rw [mmap, mmap, r4, a3, hE]
    rfl
  have d3 : ∀ q s, (rt (F.ψ q s)).map p = ((rq q).hom s).map p := fun q s => by
    rw [r4]
    exact (congrArg (fun x : Lift O _ R => x.hom s) (q3 q)).symm
  choose z z0 z1 z2 z3 using fun u : κ => obs_cocycle O ι X w Φ h2 Γ rbar r0 hbar h0 F A R p hp hs W (wf u) (co u)
    (k1 u) (k2 u) (k3 u) rt r1 r2 r3 d1 αt (fun v => (ρ v).map i) a1 a2 (fun v s => inH _ _ i _ _ (hρ v s)) hw1 d2
    rq q1 q4 d3
  have ex : ∀ j (u : {u // wf u = j}), ∃ z ∈ F.framedTwoCocycles (FormData.adRep hbar j),
      (∀ s t, (z.1 (s, t)).1 * rbar (s * t) = (rt s * rt t - rt (s * t)).map (co u)) ∧
      (∀ v s, (z.2.1 v s).1 * rbar (F.φ v s) = (rt (F.φ v s) * αt v - αt v * ((ρ v).map i).hom s).map (co u)) ∧
      ∀ q s, (z.2.2 q s).1 * rbar (F.ψ q s) = (rt (F.ψ q s) - (rq q).hom s).map (co u) := by
    rintro _ ⟨u, rfl⟩
    exact ⟨z u, z0 u, z1 u, z2 u, z3 u⟩
  clear z0 z1 z2 z3 z
  choose z z0 z1 z2 z3 using ex
  refine ⟨fun j u => Submodule.Quotient.mk ⟨z j u, z0 j u⟩, ?_⟩
  intro j _ c hc A' _ _ _ p' p'' η hp' hpp hη hη0 e1 e2
  have hx : ∑ u, residue O (c u) • z j u ∈ F.framedTwoCoboundaries (FormData.adRep hbar j) := by
    have h1 : (Submodule.Quotient.mk (∑ u, residue O (c u) • (⟨z j u, z0 j u⟩ : F.framedTwoCocycles (FormData.adRep hbar j))) :
        F.Ob (FormData.adRep hbar j)) = 0 := by
      rw [← hc, ← Submodule.mkQ_apply, map_sum]
      rfl
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, map_sum] at h1
    exact h1
  obtain ⟨μ, m1, m2⟩ := ex_mu (O := O) η hη
  have pp : ∀ x, p'' (p' x) = p x := fun x => DFunLike.congr_fun hpp x
  have key : ∀ x, p x = 0 → p' x = μ (∑ u : {u // wf u = j}, residue O (c u) * co u x) := fun x hx => by
    obtain ⟨a, ha, hxa⟩ := k4 x hx
    have : ∑ u : {u // wf u = j}, residue O (c u) * co u x = residue O (∑ u : {u // wf u = j}, a u * c u) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun u _ => by rw [map_mul, ha, mul_comm]
    rw [this, m1, Finset.sum_smul]
    conv_lhs => rw [hxa]
    rw [map_sum, ← Fintype.sum_subtype_add_sum_subtype (fun u => wf u = j),
      Finset.sum_eq_zero (s := (Finset.univ : Finset {u // ¬ wf u = j})) fun u _ => by
        rw [map_smul, e2 u u.2, smul_zero], add_zero]
    convert Finset.sum_congr rfl fun u _ => ?_
    rw [map_smul, e1, mul_smul]
  have keyM : ∀ (M N : Matrix ι ι A) (Y : {u // wf u = j} → Φ.gw (ResidueField O) j) (g : Matrix ι ι (ResidueField O)),
      M.map p = N.map p → (∀ u, (Y u).1 * g = (M - N).map (co u)) →
      M.map p' - N.map p' = ((∑ u, residue O (c u) • Y u).1 * g).map μ := fun M N Y g h1 h3 => by
    ext a b
    have h4 : p ((M - N) a b) = 0 := by
      rw [Matrix.sub_apply, map_sub, sub_eq_zero]
      exact congrFun (congrFun h1 a) b
    rw [Matrix.sub_apply, Matrix.map_apply, Matrix.map_apply, ← map_sub, ← Matrix.sub_apply, key _ h4,
      Matrix.map_apply, Submodule.coe_sum, Finset.sum_mul, Matrix.sum_apply]
    congr 1
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Submodule.coe_smul, smul_mul_assoc, h3]
    rfl
  have m3 : ∀ d, p'' (μ d) = 0 := fun d => by
    obtain ⟨a, rfl⟩ := residue_surjective d
    rw [m1, map_smul, hη0, smul_zero]
  have hp'' : Function.Surjective p'' := fun y => by
    obtain ⟨x, rfl⟩ := hp y
    exact ⟨p' x, pp x⟩
  have hs' : maximalIdeal A' * RingHom.ker p'' = ⊥ := by
    rw [eq_bot_iff, Ideal.mul_le]
    intro x hx y hy
    obtain ⟨y, rfl⟩ := hp' y
    rw [RingHom.mem_ker, pp] at hy
    rw [Ideal.mem_bot, key y hy, ← m2, (res_eq_zero_iff O A' x).2 hx, zero_mul, map_zero]
  have mm : ∀ M : Matrix ι ι A, (M.map p').map p'' = M.map p := fun M => by
    ext a b
    exact pp _
  refine (obs_correct O ι X w Φ h2 Γ rbar r0 hbar h0 F L hN hL B ρ A' R p'' hp'' hs' μ
    μ.map_add m2 m3 (p'.comp i) r (fun s => (rt s).map p') (fun s => inH _ _ p' _ _ (r1 s))
    (fun a b => ac_map p' (r2 a b)) (fun s => by rw [mm, r4]) (fun v => (αt v).map p')
    (fun v => (hh_group O ι X w Φ A).2.2.2.1 A' p' _ (a1 v))
    (by rw [a4, Matrix.map_one _ (map_zero _) (map_one _)]) (fun q => (rq q).map p')
    (fun q s => inH _ _ p' _ _ (q1 q s)) (fun q => ?_) (fun q => ?_) j _ hx (fun s t => ?_) (fun v s => ?_)
    (fun q s => ?_)).elim fun r' h => h.elim fun α' f => ⟨r', α', f.1, f.2.1, fun v => by rw [f.2.2, mm, a3]⟩
  · obtain ⟨I, hI⟩ := (hL q).closed A (rq q) (q1 q)
    refine (hI A' p').2 fun x hx => ?_
    have : x = 0 := (hI A (AlgHom.id O A)).1 (q2 q) x hx
    rw [this, map_zero]
  · rw [← q3 q]
    ext s a b
    exact pp _
  · have := keyM _ _ (fun u => (z j u).1 (s, t)) _ (d1 s t) fun u => z1 j u s t
    rw [mmap] at this
    rw [this, Prod.fst_sum, Finset.sum_apply]
    rfl
  · have := keyM _ _ (fun u => (z j u).2.1 v s) _ (d2 v s) fun u => z2 j u v s
    rw [mmap, mmap] at this
    rw [Prod.snd_sum, Prod.fst_sum, Finset.sum_apply, Finset.sum_apply]
    exact this
  · have := keyM _ _ (fun u => (z j u).2.2 q s) _ (d3 q s) fun u => z3 j u q s
    rw [Prod.snd_sum, Prod.snd_sum, Finset.sum_apply, Finset.sum_apply]
    exact this
