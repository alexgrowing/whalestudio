import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DiscreteSpectrumResidual
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CapCommuteRtInfGL
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsQr
open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

open Matrix

namespace GlobalTheory.IwasawaAdelic

theorem cornerGL_entry {R S : Type} [CommRing R] [CommRing S] {a : ℕ} (s : R →ₙ+* S)
    (g : GL (Fin a) R) (i j : Fin a) :
    (cornerGL a s g).val i j
      = (1 : Matrix (Fin a) (Fin a) S) i j - s ((1 : Matrix (Fin a) (Fin a) R) i j) + s (g.val i j) :=
  rfl

theorem cornerGL_entry_ne {R S : Type} [CommRing R] [CommRing S] {a : ℕ} (s : R →ₙ+* S)
    (g : GL (Fin a) R) {i j : Fin a} (h : i ≠ j) :
    (cornerGL a s g).val i j = s (g.val i j) := by
  rw [cornerGL_entry]; simp [Matrix.one_apply_ne h]

theorem cornerGL_entry_same {R S : Type} [CommRing R] [CommRing S] {a : ℕ} (s : R →ₙ+* S)
    (g : GL (Fin a) R) (i : Fin a) :
    (cornerGL a s g).val i i = 1 - s 1 + s (g.val i i) := by
  rw [cornerGL_entry]; simp

theorem stdBlocks_lt_of_lt {s r : ℕ} (d : Fin s → ℕ) (hd : ∑ i, d i = r) {a b : Fin s}
    (i : Fin (d a)) (j : Fin (d b)) (hba : b < a) : stdBlocks d hd ⟨b, j⟩ < stdBlocks d hd ⟨a, i⟩ := by
  let f : ℕ → ℕ := fun n => if h : n < s then d ⟨n, h⟩ else 0
  have key : ∀ c : Fin s, ∑ x : Fin c, d (Fin.castLE c.2.le x) = ∑ x ∈ Finset.range c, f x := by
    intro c
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun x _ => ?_
    have hx : (x : ℕ) < s := x.2.trans c.2
    simp only [f, hx, dif_pos]
    rfl
  rw [Fin.lt_def, stdBlocks_val, stdBlocks_val, key, key]
  have h1 : ∑ x ∈ Finset.range (b + 1), f x ≤ ∑ x ∈ Finset.range a, f x :=
    Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.succ_le_of_lt hba))
  rw [Finset.sum_range_succ] at h1
  have h2 : f b = d b := by simp [f]
  have := j.2
  omega

theorem mem_parab_of_upper {R : Type} [CommRing R] {c N : ℕ} (n : Fin c → ℕ) (h : ∑ i, n i = N)
    (b : GL (Fin N) R) (hb : (b : Matrix (Fin N) (Fin N) R).BlockTriangular id) :
    b ∈ parab R (stdBlocks n h) := by
  rw [mem_parab_iff]
  intro a a' i j hlt
  exact hb (stdBlocks_lt_of_lt n h i j hlt)

theorem exists_upper_mul_unitary (N : ℕ) (y : GL (Fin N) ℂ) :
    ∃ b : GL (Fin N) ℂ, (b : Matrix (Fin N) (Fin N) ℂ).BlockTriangular id ∧
      ∃ k : Matrix (Fin N) (Fin N) ℂ, k ∈ Matrix.unitaryGroup (Fin N) ℂ ∧
        (y : Matrix (Fin N) (Fin N) ℂ) = b * k := by
  set A : Matrix (Fin N) (Fin N) ℂ := ((y⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) with hAdef
  have hyA : (y : Matrix (Fin N) (Fin N) ℂ) * A = 1 := by simp [hAdef]
  have hAdet : IsUnit A.det := by
    rw [← Matrix.isUnit_iff_isUnit_det]; exact (y⁻¹).isUnit
  have hdet : IsUnit (Aᴴ * A).det := by
    rw [det_mul, det_conjTranspose]; exact hAdet.star.mul hAdet
  obtain ⟨Q, u, hQ, hu, hudet, hA⟩ := GlobalTheory.QRDecomp.exists_qr N N A hdet
  letI := u.invertibleOfIsUnitDet hudet
  refine ⟨(Matrix.nonsingInvUnit u hudet)⁻¹, ?_, Qᴴ, ?_, ?_⟩
  · show (u⁻¹).BlockTriangular id
    exact Matrix.blockTriangular_inv_of_blockTriangular hu
  · rw [Matrix.mem_unitaryGroup_iff', star_eq_conjTranspose, conjTranspose_conjTranspose]
    exact mul_eq_one_comm.1 hQ
  · show (y : Matrix (Fin N) (Fin N) ℂ) = u⁻¹ * Qᴴ
    have hQQ : Q * Qᴴ = 1 := mul_eq_one_comm.1 hQ
    have h1 : (Q * u) * (u⁻¹ * Qᴴ) = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc u, Matrix.mul_nonsing_inv u hudet, Matrix.one_mul, hQQ]
    calc (y : Matrix (Fin N) (Fin N) ℂ) = (y : Matrix (Fin N) (Fin N) ℂ) * ((Q * u) * (u⁻¹ * Qᴴ)) := by
          rw [h1, Matrix.mul_one]
      _ = u⁻¹ * Qᴴ := by rw [← Matrix.mul_assoc, ← hA, hyA, Matrix.one_mul]

theorem ext_eval {ι : Type} {N : ℕ} {P Q : Matrix (Fin N) (Fin N) (ι → ℂ)}
    (hPQ : ∀ v, P.map (Pi.evalRingHom (fun _ : ι => ℂ) v) = Q.map (Pi.evalRingHom (fun _ : ι => ℂ) v)) :
    P = Q := by
  ext i j v; exact congrFun (congrFun (hPQ v) i) j

theorem exists_upper_mul_unitary_inf (E : Type) [Field E] (N : ℕ) (y : GL (Fin N) (Cinf E)) :
    ∃ b : GL (Fin N) (Cinf E), (b : Matrix (Fin N) (Fin N) (Cinf E)).BlockTriangular id ∧
      ∃ k : Kinf E N, y = b * Unitary.toUnits k := by
  let ev : InfinitePlace E → (Cinf E →+* ℂ) := fun v => Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) v
  choose B hB K hK hyK using fun v => exists_upper_mul_unitary N (Matrix.GeneralLinearGroup.map (ev v) y)
  let bm : Matrix (Fin N) (Fin N) (Cinf E) := fun i j v => (B v : Matrix (Fin N) (Fin N) ℂ) i j
  let bi : Matrix (Fin N) (Fin N) (Cinf E) := fun i j v => (((B v)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j
  let km : Matrix (Fin N) (Fin N) (Cinf E) := fun i j v => K v i j
  have hbm : ∀ v, bm.map (ev v) = (B v : Matrix (Fin N) (Fin N) ℂ) := fun v => rfl
  have hbi : ∀ v, bi.map (ev v) = (((B v)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) := fun v => rfl
  have hkm : ∀ v, km.map (ev v) = K v := fun v => rfl
  have h1 : bm * bi = 1 := ext_eval fun v => by
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), hbm, hbi]; simp
  have h2 : bi * bm = 1 := ext_eval fun v => by
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), hbm, hbi]; simp
  have hkU : km ∈ Matrix.unitaryGroup (Fin N) (Cinf E) := by
    rw [Matrix.mem_unitaryGroup_iff']
    refine ext_eval fun v => ?_
    have hs : (star km).map (ev v) = star (K v) := by
      ext i j; rfl
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), hs, hkm]
    exact (Matrix.mem_unitaryGroup_iff').1 (hK v)
  refine ⟨⟨bm, bi, h1, h2⟩, ?_, ⟨km, hkU⟩, ?_⟩
  · intro i j hij
    funext v
    exact hB v hij
  · apply Units.ext
    refine ext_eval fun v => ?_
    show (y : Matrix (Fin N) (Fin N) (Cinf E)).map (ev v) = (bm * km).map (ev v)
    rw [Matrix.map_mul, hbm, hkm]
    exact hyK v

theorem infGL_eq (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ) :
    infGL E N = cornerGL N (GlobalTheory.CuspRep.sInf E) := rfl

theorem infGL_mem_unipRad (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] {c N : ℕ}
    (n : Fin c → ℕ) (h : ∑ i, n i = N) (u : GL (Fin N) (Cinf E))
    (hu : u ∈ unipRad (Cinf E) (stdBlocks n h)) : infGL E N u ∈ unipRad (Ad E) (stdBlocks n h) := by
  rw [mem_unipRad] at hu ⊢
  obtain ⟨hP, hD⟩ := hu
  refine ⟨mem_parab_iff.2 fun a b i j hlt => ?_, fun a i j => ?_⟩
  · have hne : stdBlocks n h ⟨a, i⟩ ≠ stdBlocks n h ⟨b, j⟩ := fun he => by
      have := congrArg Sigma.fst ((stdBlocks n h).injective he)
      exact (ne_of_gt hlt) this
    rw [infGL_eq, cornerGL_entry_ne _ _ hne, mem_parab_iff.1 hP a b i j hlt, map_zero]
  · by_cases hij : i = j
    · subst hij
      rw [infGL_eq, cornerGL_entry_same, hD a i i]; simp
    · have hne : stdBlocks n h ⟨a, i⟩ ≠ stdBlocks n h ⟨a, j⟩ := fun he => by
        exact hij (by simpa using (stdBlocks n h).injective he)
      rw [infGL_eq, cornerGL_entry_ne _ _ hne, hD a i j, Matrix.one_apply_ne hij, Matrix.one_apply_ne hij,
        map_zero]

theorem infGL_leviEmb (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] {c N : ℕ}
    (n : Fin c → ℕ) (h : ∑ i, n i = N) (l : ∀ i, GL (Fin (n i)) (Cinf E)) :
    infGL E N (leviEmb (Cinf E) (stdBlocks n h) l)
      = leviEmb (Ad E) (stdBlocks n h) (fun i => infGL E (n i) (l i)) := by
  apply Units.ext
  ext p q
  obtain ⟨⟨a, i⟩, rfl⟩ := (stdBlocks n h).surjective p
  obtain ⟨⟨b, j⟩, rfl⟩ := (stdBlocks n h).surjective q
  by_cases hab : a = b
  · subst hab
    rw [leviEmb_apply_same]
    by_cases hij : i = j
    · subst hij
      rw [infGL_eq, infGL_eq, cornerGL_entry_same, cornerGL_entry_same, leviEmb_apply_same]
    · have hne : stdBlocks n h ⟨a, i⟩ ≠ stdBlocks n h ⟨a, j⟩ := fun he =>
        hij (by simpa using (stdBlocks n h).injective he)
      rw [infGL_eq, infGL_eq, cornerGL_entry_ne _ _ hne, cornerGL_entry_ne _ _ hij, leviEmb_apply_same]
  · have hne : stdBlocks n h ⟨a, i⟩ ≠ stdBlocks n h ⟨b, j⟩ := fun he =>
      hab (congrArg Sigma.fst ((stdBlocks n h).injective he))
    rw [leviEmb_apply_ne _ _ _ hab, infGL_eq, cornerGL_entry_ne _ _ hne, leviEmb_apply_ne _ _ _ hab, map_zero]

theorem iwasawa : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] {c N : ℕ} (n : Fin c → ℕ) (h : ∑ i, n i = N) (x : GA E N), ∃ u ∈ unipRad (Ad E) (stdBlocks n h), ∃ (m : ∀ i, GA E (n i)) (k : Kinf E N) (g : GL (Fin N) (Af E)), x = u * leviEmb (Ad E) (stdBlocks n h) m * (infGL E N (Unitary.toUnits k) * finGL E N g) := by
  intro E _ _ _ c N n h x
  obtain ⟨b, hb, k, hy⟩ := exists_upper_mul_unitary_inf E N (Matrix.GeneralLinearGroup.map (pInf E) x)
  obtain ⟨u, hu, hbu⟩ := exists_levi_mul_unip (Cinf E) (stdBlocks n h) ⟨b, mem_parab_of_upper n h b hb⟩
  set L := leviEmb (Cinf E) (stdBlocks n h) (leviProj (Cinf E) (stdBlocks n h) ⟨b, mem_parab_of_upper n h b hb⟩) with hL
  have hN := leviEmb_mem_normalizer (Cinf E) (stdBlocks n h) (leviProj (Cinf E) (stdBlocks n h) ⟨b, mem_parab_of_upper n h b hb⟩)
  have hu' : L * u * L⁻¹ ∈ unipRad (Cinf E) (stdBlocks n h) := (Subgroup.mem_normalizer_iff.1 hN u).1 hu
  refine ⟨infGL E N (L * u * L⁻¹), infGL_mem_unipRad E n h _ hu', fun i => infGL E (n i) (leviProj (Cinf E) (stdBlocks n h) ⟨b, mem_parab_of_upper n h b hb⟩ i), k, Matrix.GeneralLinearGroup.map (pFin E) x, ?_⟩
  rw [← infGL_leviEmb, ← hL]
  conv_lhs => rw [← infGL_mul_finGL x, hy]
  simp only [Subtype.coe_mk] at hbu
  rw [hbu]
  simp only [map_mul, map_inv]
  group

end GlobalTheory.IwasawaAdelic
