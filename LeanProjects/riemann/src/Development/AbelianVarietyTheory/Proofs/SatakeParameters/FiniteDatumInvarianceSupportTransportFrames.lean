import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DatTransport

section Gen

variable {E : Type} [Field E] [NumberField E]

theorem mem_localization_of_smul_mem₂ {W : Type} [AddCommGroup W] [Module (𝓞 E) W] (q : Ideal (𝓞 E)) [q.IsPrime] (L : Submodule (𝓞 E) W)
    {t : 𝓞 E} (ht : t ∈ q.primeCompl) {v : W} (h : t • v ∈ Formalism.HermitianLatticesTheory.localization₂ q L) : v ∈ Formalism.HermitianLatticesTheory.localization₂ q L := by
  obtain ⟨u, hu, huv⟩ := h
  exact ⟨u * t, q.primeCompl.mul_mem hu ht, by rw [mul_smul]; exact huv⟩

theorem mem_localization_map_iff {n : ℕ} (f : (Fin n → E) ≃ₗ[E] (Fin n → E)) (q : Ideal (𝓞 E)) [q.IsPrime]
    (L : Submodule (𝓞 E) (Fin n → E)) (y : Fin n → E) :
    y ∈ Formalism.HermitianLatticesTheory.localization₂ q (L.map (f.toLinearMap.restrictScalars (𝓞 E))) ↔ f.symm y ∈ Formalism.HermitianLatticesTheory.localization₂ q L := by
  have hf : ∀ (r : 𝓞 E) (v : Fin n → E), f (r • v) = r • f v := fun r v => (f.toLinearMap.restrictScalars (𝓞 E)).map_smul r v
  constructor
  · rintro ⟨r, hr, z, hz, hzy⟩
    refine ⟨r, hr, ?_⟩
    have e1 : r • f.symm y = z := by
      apply f.injective
      rw [hf, f.apply_symm_apply]
      exact hzy.symm
    rw [e1]
    exact hz
  · rintro ⟨r, hr, hy⟩
    refine ⟨r, hr, r • f.symm y, hy, ?_⟩
    show f (r • f.symm y) = r • y
    rw [hf, f.apply_symm_apply]

end Gen

end GlobalTheory.DatTransport

namespace GlobalTheory.DatTransport

section PerO

variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}

theorem perO_apply_mem (AA : Submodule (𝓞 E) E) (q : Ideal (𝓞 E)) [q.IsPrime]
    (hAA : AA ≤ Formalism.HermitianLatticesTheory.localization₂ q (1 : Submodule (𝓞 E) E)) (M : Submodule (𝓞 E) (Sp E a)) (M' : Submodule (𝓞 E) (Sp E b))
    (w : HomE E a b) (hw : w ∈ Formalism.HermitianLatticesTheory.localization₂ q (perO AA M M')) :
    ∀ y ∈ Formalism.HermitianLatticesTheory.localization₂ q M, w y ∈ Formalism.HermitianLatticesTheory.localization₂ q M' := by
  intro y hy
  obtain ⟨t, ht, htw⟩ := hw
  have key : ∀ z ∈ perO AA M M', z y ∈ Formalism.HermitianLatticesTheory.localization₂ q M' := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨r, hr, x, hx, rfl⟩ := hz
      obtain ⟨t1, ht1, hy1⟩ := hy
      have hxy : t1 • x y ∈ M' := by
        have e0 : x (t1 • y) = t1 • x y := (x.restrictScalars (𝓞 E)).map_smul t1 y
        rw [← e0]
        exact hx _ hy1
      obtain ⟨t2, ht2, hr2⟩ := hAA hr
      obtain ⟨o, ho⟩ := Submodule.mem_one.1 hr2
      refine ⟨t2 * t1, q.primeCompl.mul_mem ht2 ht1, ?_⟩
      have e1 : (t2 * t1) • ((r • x) y) = o • (t1 • x y) := by
        funext l
        rw [Algebra.smul_def] at ho
        simp only [LinearMap.smul_apply, Pi.smul_apply, Algebra.smul_def, smul_eq_mul, map_mul, ho, Pi.mul_apply,
          Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
        ring
      rw [e1]
      exact M'.smul_mem o hxy
    | zero => exact zero_mem _
    | add z z' _ _ h1 h2 =>
      rw [LinearMap.add_apply]
      exact add_mem h1 h2
    | smul c z _ h =>
      rw [LinearMap.smul_apply]
      exact Submodule.smul_mem _ c h
  have h1 := key _ htw
  rw [LinearMap.smul_apply] at h1
  exact mem_localization_of_smul_mem₂ q M' ht h1

end PerO

end GlobalTheory.DatTransport

namespace GlobalTheory.DatTransport

section Seam

variable {D : D7} {X : Fields} (s : Seam D X)

theorem tr_smul {n : ℕ} (c : 𝓞 X.E) (x : Sp X.E n) :
    (fun i => s.iE ((c • x) i)) = RingOfIntegers.mapRingEquiv s.iE c • (fun i => s.iE (x i)) := by
  funext i
  simp only [Pi.smul_apply, Algebra.smul_def, map_mul]
  rfl

theorem mem_seamLat_iff {n : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E n)) (y : Fin n → D.host.E) :
    y ∈ s.lat N ↔ ∃ x ∈ N, (fun i => s.iE (x i)) = y := by
  constructor
  · intro hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact hy
    | zero => exact ⟨0, N.zero_mem, by funext i; simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨a, ha, rfl⟩ := hy
      obtain ⟨b, hb, rfl⟩ := hz
      exact ⟨a + b, N.add_mem ha hb, by funext i; simp⟩
    | smul r y _ hy =>
      obtain ⟨a, ha, rfl⟩ := hy
      refine ⟨(RingOfIntegers.mapRingEquiv s.iE).symm r • a, N.smul_mem _ ha, ?_⟩
      rw [tr_smul, RingEquiv.apply_symm_apply]
  · rintro ⟨x, hx, rfl⟩
    exact Submodule.subset_span ⟨x, hx, rfl⟩

theorem tr_injective {n : ℕ} : Function.Injective (fun (x : Sp X.E n) (i : Fin n) => s.iE (x i)) := by
  intro x y h
  funext i
  exact s.iE.injective (congrFun h i)

theorem mem_localization_seamLat_iff (P : HeightOneSpectrum (𝓞 X.E)) {n : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E n)) (x : Sp X.E n) :
    x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N ↔ (fun i => s.iE (x i)) ∈ Formalism.HermitianLatticesTheory.localization₂ (seamP s P).asIdeal (s.lat N) := by
  constructor
  · rintro ⟨c, hc, hcx⟩
    refine ⟨RingOfIntegers.mapRingEquiv s.iE c, fun h => hc ((mem_seamP s P c).1 h), ?_⟩
    rw [← tr_smul]
    exact (mem_seamLat_iff s N _).2 ⟨_, hcx, rfl⟩
  · rintro ⟨d, hd, hdx⟩
    obtain ⟨c, rfl⟩ := (RingOfIntegers.mapRingEquiv s.iE).surjective d
    refine ⟨c, fun h => hd ((mem_seamP s P c).2 h), ?_⟩
    rw [← tr_smul] at hdx
    obtain ⟨x', hx', e⟩ := (mem_seamLat_iff s N _).1 hdx
    rw [tr_injective s e] at hx'
    exact hx'

theorem aaOf_le_locP_seamP (cc : Ideal (𝓞 D.host.K)) (Q : HeightOneSpectrum (𝓞 X.E))
    (h : Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal (Submodule.span (𝓞 X.E) {r | ∃ c ∈ cc, ∃ t ∈ D.host.AA0,
      r = s.iE.symm ((((c : 𝓞 D.host.K) : D.host.K) : D.host.E) * t)}) = Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal (1 : Submodule (𝓞 X.E) X.E)) :
    Formalism.L2.PairingIndexBounds.F.aaOf D cc ≤ Formalism.HermitianLatticesTheory.localization₂ (seamP s Q).asIdeal (1 : Submodule (𝓞 D.host.E) D.host.E) := by
  unfold Formalism.L2.PairingIndexBounds.F.aaOf
  rw [Submodule.span_le]
  rintro _ ⟨c, hc, t, ht, rfl⟩
  have h1 : s.iE.symm ((((c : 𝓞 D.host.K) : D.host.K) : D.host.E) * t) ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal (1 : Submodule (𝓞 X.E) X.E) := by
    rw [← h]
    exact ⟨1, Q.asIdeal.primeCompl.one_mem, by rw [one_smul]; exact Submodule.subset_span ⟨c, hc, t, ht, rfl⟩⟩
  obtain ⟨u, hu, hu1⟩ := h1
  obtain ⟨o, ho⟩ := Submodule.mem_one.1 hu1
  refine ⟨RingOfIntegers.mapRingEquiv s.iE u, fun hh => hu ((mem_seamP s Q u).1 hh), ?_⟩
  refine Submodule.mem_one.2 ⟨RingOfIntegers.mapRingEquiv s.iE o, ?_⟩
  rw [Algebra.smul_def] at ho ⊢
  have e1 := congrArg s.iE ho
  rw [map_mul, RingEquiv.apply_symm_apply] at e1
  exact e1

end Seam

end GlobalTheory.DatTransport

namespace GlobalTheory.DatTransport

section Hom

variable {D : D7} {X : Fields} (s : Seam D X) {a b : ℕ}

theorem seam_inFr_apply (f : (Fin a → D.host.E) ≃ₗ[D.host.E] (Fin a → D.host.E))
    (f' : (Fin b → D.host.E) ≃ₗ[D.host.E] (Fin b → D.host.E)) (w : HomE D.host.E a b) (u : Sp X.E a) :
    (fun l => s.iE (seamHom s (inFr f f' w) u l)) = f'.symm (w (f (fun k => s.iE (u k)))) := by
  funext l
  rw [seamHom_apply]
  rfl

theorem homAtP_iff (Q : HeightOneSpectrum (𝓞 X.E)) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b))
    (f : (Fin a → D.host.E) ≃ₗ[D.host.E] (Fin a → D.host.E)) (f' : (Fin b → D.host.E) ≃ₗ[D.host.E] (Fin b → D.host.E))
    (w : HomE D.host.E a b) :
    (∀ y ∈ Formalism.HermitianLatticesTheory.localization₂ (seamP s Q).asIdeal ((s.lat N).map (f.toLinearMap.restrictScalars (𝓞 D.host.E))),
        w y ∈ Formalism.HermitianLatticesTheory.localization₂ (seamP s Q).asIdeal ((s.lat N').map (f'.toLinearMap.restrictScalars (𝓞 D.host.E)))) ↔
      ∀ u ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal N, seamHom s (inFr f f' w) u ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal N' := by
  have hi : ∀ u : Sp X.E a, f (fun k => s.iE (u k)) ∈
      Formalism.HermitianLatticesTheory.localization₂ (seamP s Q).asIdeal ((s.lat N).map (f.toLinearMap.restrictScalars (𝓞 D.host.E))) ↔
        u ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal N := by
    intro u
    rw [mem_localization_map_iff, f.symm_apply_apply, ← mem_localization_seamLat_iff]
  constructor
  · intro h u hu
    rw [mem_localization_seamLat_iff s Q N', seam_inFr_apply]
    exact (mem_localization_map_iff f' _ _ _).1 (h _ ((hi u).2 hu))
  · intro h y hy
    have hyu : y = f (fun k => s.iE ((fun k => s.iE.symm ((f.symm y) k)) k)) := by
      simp
    rw [hyu] at hy ⊢
    have h1 := (mem_localization_seamLat_iff s Q N' _).1 (h _ ((hi _).1 hy))
    rw [seam_inFr_apply] at h1
    exact (mem_localization_map_iff f' _ _ _).2 h1

theorem mem_homAt_iff (S : Finset (HeightOneSpectrum (𝓞 X.E))) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b))
    (f : (Fin a → D.host.E) ≃ₗ[D.host.E] (Fin a → D.host.E)) (f' : (Fin b → D.host.E) ≃ₗ[D.host.E] (Fin b → D.host.E))
    (w : HomE D.host.E a b) :
    w ∈ homAt (S.map (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s.iE)).toEmbedding)
        ((s.lat N).map (f.toLinearMap.restrictScalars (𝓞 D.host.E))) ((s.lat N').map (f'.toLinearMap.restrictScalars (𝓞 D.host.E))) ↔
      seamHom s (inFr f f' w) ∈ homAt S N N' := by
  constructor
  · intro h Q hQ
    exact (homAtP_iff s Q N N' f f' w).1 (h (seamP s Q) (Finset.mem_map_of_mem _ hQ))
  · intro h P hP
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_map.1 hP
    exact (homAtP_iff s Q N N' f f' w).2 (h Q hQ)

theorem seamHom_inFr_sub (f : (Fin a → D.host.E) ≃ₗ[D.host.E] (Fin a → D.host.E))
    (f' : (Fin b → D.host.E) ≃ₗ[D.host.E] (Fin b → D.host.E)) (w w' : HomE D.host.E a b) :
    seamHom s (inFr f f' (w - w')) = seamHom s (inFr f f' w) - seamHom s (inFr f f' w') := by
  refine LinearMap.ext fun u => funext fun l => s.iE.injective ?_
  have e1 := congrFun (seam_inFr_apply s f f' (w - w') u) l
  have e2 := congrFun (seam_inFr_apply s f f' w u) l
  have e3 := congrFun (seam_inFr_apply s f f' w' u) l
  rw [e1]
  simp only [LinearMap.sub_apply, map_sub, Pi.sub_apply]
  rw [e2, e3]

theorem seamHom_inFr_natCast_smul (f : (Fin a → D.host.E) ≃ₗ[D.host.E] (Fin a → D.host.E))
    (f' : (Fin b → D.host.E) ≃ₗ[D.host.E] (Fin b → D.host.E)) (c : ℕ) (w : HomE D.host.E a b) :
    seamHom s (inFr f f' ((c : 𝓞 D.host.E) • w)) = (c : 𝓞 X.E) • seamHom s (inFr f f' w) := by
  refine LinearMap.ext fun u => funext fun l => s.iE.injective ?_
  have e1 := congrFun (seam_inFr_apply s f f' ((c : 𝓞 D.host.E) • w) u) l
  have e2 := congrFun (seam_inFr_apply s f f' w u) l
  rw [e1]
  simp only [LinearMap.smul_apply, Nat.cast_smul_eq_nsmul, map_nsmul, Pi.smul_apply]
  rw [e2]

end Hom

end GlobalTheory.DatTransport

namespace GlobalTheory.DatTransport

theorem datLoc_seam_inFr : ∀ {D : D7} {X : Fields} (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (S : Finset (HeightOneSpectrum (𝓞 X.E))) {a b : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (f : (Fin a → D.host.E) ≃ₗ[D.host.E] (Fin a → D.host.E)) (f' : (Fin b → D.host.E) ≃ₗ[D.host.E] (Fin b → D.host.E)) (cA cB : ℕ), 0 < cA → 0 < cB → ∀ (Ξ : HomE X.E a b → X.K), (∀ P ∈ S, Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Submodule.span (𝓞 X.E) {r | ∃ c ∈ cc, ∃ t ∈ D.host.AA0, r = s.iE.symm ((((c : 𝓞 D.host.K) : D.host.K) : D.host.E) * t)}) = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (1 : Submodule (𝓞 X.E) X.E)) → (∀ x, Ξ x ≠ 0 → x ∈ divLat cA (homAt S N N')) → (∀ x, ∀ y ∈ mulLat cB (homAt S N N'), Ξ (x + y) = Ξ x) → DatLoc D cc (S.map (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s.iE)).toEmbedding) (cA * cB) ((s.lat N).map (f.toLinearMap.restrictScalars (𝓞 D.host.E))) ((s.lat N').map (f'.toLinearMap.restrictScalars (𝓞 D.host.E))) (fun z => s.σ₀ (Ξ (seamHom s (inFr f f' z)))) ∧ ∀ z, s.σ₀ (Ξ (seamHom s (inFr f f' z))) ≠ 0 → z ∈ divLat (cA * cB) (homAt (S.map (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s.iE)).toEmbedding) ((s.lat N).map (f.toLinearMap.restrictScalars (𝓞 D.host.E))) ((s.lat N').map (f'.toLinearMap.restrictScalars (𝓞 D.host.E)))) := by
  intro D X s cc S a b N N' f f' cA cB hA hB Ξ hAA hsupp hinv
  have hH := mem_homAt_iff s S N N' f f'
  constructor
  · intro x x' hx
    have hAA' : ∀ P ∈ S.map (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s.iE)).toEmbedding,
        Formalism.L2.PairingIndexBounds.F.aaOf D cc ≤ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (1 : Submodule (𝓞 D.host.E) D.host.E) := by
      intro P hP
      obtain ⟨Q, hQ, rfl⟩ := Finset.mem_map.1 hP
      exact aaOf_le_locP_seamP s cc Q (hAA Q hQ)
    set d := (((cA * cB : ℕ) : D.host.E))⁻¹ • (x - x') with hd
    have hdH : d ∈ homAt (S.map (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s.iE)).toEmbedding)
        ((s.lat N).map (f.toLinearMap.restrictScalars (𝓞 D.host.E))) ((s.lat N').map (f'.toLinearMap.restrictScalars (𝓞 D.host.E))) :=
      fun P hP y hy => perO_apply_mem _ P.asIdeal (hAA' P hP) _ _ d (hx P hP) y hy
    have hne : ((cA * cB : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (Nat.mul_ne_zero hA.ne' hB.ne')
    have hxx : x - x' = ((cA * cB : ℕ) : 𝓞 D.host.E) • d := by
      rw [hd, Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul D.host.E, smul_smul, mul_inv_cancel₀ hne, one_smul]
    have hu : (cA : 𝓞 X.E) • seamHom s (inFr f f' d) ∈ homAt S N N' :=
      Submodule.smul_mem _ _ ((hH d).1 hdH)
    have hm : seamHom s (inFr f f' x) - seamHom s (inFr f f' x') ∈ mulLat cB (homAt S N N') := by
      rw [← seamHom_inFr_sub, hxx, seamHom_inFr_natCast_smul, Nat.cast_mul, mul_comm, mul_smul]
      exact ⟨_, hu, rfl⟩
    show s.σ₀ (Ξ (seamHom s (inFr f f' x))) = s.σ₀ (Ξ (seamHom s (inFr f f' x')))
    rw [← hinv (seamHom s (inFr f f' x')) _ hm, add_sub_cancel]
  · intro z hz
    have h1 : Ξ (seamHom s (inFr f f' z)) ≠ 0 := fun h => hz (by rw [h, map_zero])
    have h2 : (cA : 𝓞 X.E) • seamHom s (inFr f f' z) ∈ homAt S N N' := hsupp _ h1
    have h3 := (hH ((cA : 𝓞 D.host.E) • z)).2 (by rw [seamHom_inFr_natCast_smul]; exact h2)
    rw [Formalism.L2.Col.divLat, Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply, Nat.cast_mul, mul_comm, mul_smul]
    exact Submodule.smul_mem _ _ h3

end GlobalTheory.DatTransport
