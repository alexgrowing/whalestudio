import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ZmodToQZ
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.QzInj

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

private theorem embQ_smul (l : ℕ) [Fact l.Prime] {M : Type} [AddCommGroup M] [Module ℤ_[l] M] (z : ℤ_[l]) (x : M)
    (hx : (l : ℤ_[l]) • x = 0) : z • x = z.zmodRepr • x := by
  have hm := PadicInt.sub_zmodRepr_mem z
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at hm
  obtain ⟨b, hb⟩ := hm
  calc z • x = (z - (z.zmodRepr : ℤ_[l])) • x + (z.zmodRepr : ℤ_[l]) • x := by
        rw [sub_smul, sub_add_cancel]
    _ = z.zmodRepr • x := by
        rw [← hb, mul_smul, hx, smul_zero, zero_add, Nat.cast_smul_eq_nsmul]

private theorem embQ_fl (l : ℕ) [hl : Fact l.Prime] (T : Type) [AddCommGroup T] (r : ℕ) (hTn : ∀ x : T, l • x = 0)
    (hcard : CardLe T (l ^ r)) : ∃ g : T →+ (Fin r → ZMod l), Function.Injective g := by
  obtain ⟨hfin, hc⟩ := hcard
  letI : Module (ZMod l) T := AddCommGroup.zmodModule hTn
  haveI := Fintype.ofFinite T
  haveI hF : Module.Finite (ZMod l) T := Module.Finite.of_finite
  haveI hFr : Module.Free (ZMod l) T := Module.Free.of_divisionRing (ZMod l) T
  set d := Module.finrank (ZMod l) T with hd_def
  have hcardT : Fintype.card T = l ^ d := by
    rw [Module.card_eq_pow_finrank (K := ZMod l) (V := T), ZMod.card]
  have hd : d ≤ r := by
    have : l ^ d ≤ l ^ r := by rw [← hcardT, ← Nat.card_eq_fintype_card]; exact hc
    exact (Nat.pow_le_pow_iff_right hl.out.one_lt).mp this
  let b := @Module.finBasis (ZMod l) T _ _ _ hFr _ hF
  let E := b.equivFun
  have hadd : ∀ s t : T, E.toFun (s + t) = E.toFun s + E.toFun t := E.map_add'
  have hzero : E.toFun 0 = 0 := by
    have := hadd 0 0
    simp only [add_zero] at this
    exact left_eq_add.mp this
  let g : T →+ (Fin r → ZMod l) :=
    { toFun := fun t i => if h : (i : ℕ) < d then E.toFun t ⟨i, h⟩ else 0
      map_zero' := by
        funext i
        by_cases h : (i : ℕ) < d
        · simp only [h, dif_pos, hzero, Pi.zero_apply]
        · simp only [h, dif_neg, not_false_eq_true, Pi.zero_apply]
      map_add' := by
        intro s t
        funext i
        by_cases h : (i : ℕ) < d
        · simp only [h, dif_pos, hadd, Pi.add_apply]
        · simp only [h, dif_neg, not_false_eq_true, Pi.add_apply, add_zero] }
  refine ⟨g, ?_⟩
  intro s t hst
  have key : E.toFun s = E.toFun t := by
    funext j
    have := congr_fun hst (Fin.castLE hd j)
    simp only [g, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Fin.coe_castLE, Fin.eta] at this
    rwa [dif_pos j.isLt, dif_pos j.isLt] at this
  calc s = E.invFun (E.toFun s) := (E.left_inv s).symm
    _ = E.invFun (E.toFun t) := by rw [key]
    _ = t := E.left_inv t

theorem UpperTheory.V.Two.embedQZ :
    ∀ (l : ℕ) [Fact l.Prime] (D : Type) [AddCommGroup D] [Module ℤ_[l] D] (r : ℕ), (∀ x : D, ∃ k : ℕ, (l : ℤ_[l]) ^ k • x = 0) → CardLe (Submodule.torsionBy ℤ_[l] D (l : ℤ_[l])) (l ^ r) →
      ∃ f : D →ₗ[ℤ_[l]] (Fin r → QZ l), Function.Injective f := by
  intro l _ D _ _ r htors hcard
  set Tl := Submodule.torsionBy ℤ_[l] D (l : ℤ_[l]) with hTl
  have hTl' : ∀ t : Tl, (l : ℤ_[l]) • t = 0 := by
    intro t
    have h := t.2
    rw [Submodule.mem_torsionBy_iff] at h
    exact Subtype.ext h
  have hTn : ∀ t : Tl, l • t = 0 := by
    intro t
    rw [← Nat.cast_smul_eq_nsmul ℤ_[l]]
    exact hTl' t
  obtain ⟨g, hg⟩ := embQ_fl l Tl r hTn hcard
  obtain ⟨ι, hιinj, hιrange, -⟩ := UpperTheory.V.Kum.zmodToQZ l 1
  let e : ZMod l ≃+* ZMod (l ^ 1) := ZMod.ringEquivCongr (pow_one l).symm
  have hιl : ∀ a, (l : ℤ_[l]) • ι a = 0 := by
    intro a
    have := (hιrange (ι a)).mp ⟨a, rfl⟩
    simpa using this
  let ψ : Fin r → Tl →+ QZ l := fun i =>
    ((ι : ZMod (l ^ 1) →+ QZ l).comp e.toAddMonoidHom).comp ((Pi.evalAddMonoidHom (fun _ => ZMod l) i).comp g)
  have hψl : ∀ i t, (l : ℤ_[l]) • ψ i t = 0 := fun i t => hιl _
  let ψL : Fin r → Tl →ₗ[ℤ_[l]] QZ l := fun i =>
    { toFun := ψ i
      map_add' := (ψ i).map_add
      map_smul' := by
        intro z t
        simp only [RingHom.id_apply]
        rw [embQ_smul l z t (hTl' t), map_nsmul, ← embQ_smul l z (ψ i t) (hψl i t)] }
  have hext := fun i => (UpperTheory.V.PropA.qzInj l).out Tl.subtype Subtype.val_injective (ψL i)
  choose y hy using hext
  refine ⟨LinearMap.pi y, ?_⟩
  have hzeroT : ∀ t : Tl, (∀ i, y i t = 0) → t = 0 := by
    intro t ht
    have hgt : g t = 0 := by
      funext i
      have h1 := hy i t
      rw [Submodule.coe_subtype, ht i] at h1
      have h2 : ι (e (g t i)) = ι 0 := by
        rw [map_zero]
        exact h1.symm
      have h3 := hιinj h2
      simpa using h3
    exact hg (by rw [hgt, map_zero])
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hxi : ∀ x : D, LinearMap.pi y x = 0 → ∀ i, y i x = 0 := by
    intro x hx i
    have := congr_fun hx i
    simpa using this
  obtain ⟨k, hk⟩ := htors x
  induction k generalizing x with
  | zero =>
    simpa using hk
  | succ k ih =>
    have hlx : (l : ℤ_[l]) • x = 0 := by
      apply ih ((l : ℤ_[l]) • x)
      · rw [map_smul, hx, smul_zero]
      · rw [← mul_smul, ← pow_succ]
        exact hk
    have hmem : x ∈ Tl := (Submodule.mem_torsionBy_iff _ _).mpr hlx
    have := hzeroT ⟨x, hmem⟩ (hxi x hx)
    simpa using congrArg Subtype.val this
