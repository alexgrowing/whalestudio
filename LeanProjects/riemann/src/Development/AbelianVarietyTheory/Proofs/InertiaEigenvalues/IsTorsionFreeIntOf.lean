import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsInertTop
import Formalism.LocalToGlobal.ProjectiveLattices.FullExists

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.ConstBound

theorem isTorsionFree_int_of {E : Type} [Field E] [NumberField E] (X : Type) [AddCommGroup X] [Module (𝓞 E) X]
    [Module.IsTorsionFree (𝓞 E) X] : Module.IsTorsionFree ℤ X :=
  Module.IsTorsionFree.trans_faithfulSMul ℤ (𝓞 E) X

theorem datum_free {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} (Dw : Datum H) :
    Module.Free ℤ Dw.La ∧ Module.Finite ℤ Dw.La := by
  have := Dw.fin
  have := Dw.proj
  have : Module.IsTorsionFree ℤ Dw.La := isTorsionFree_int_of (E := E) Dw.La
  have : Module.Finite ℤ Dw.La := Module.Finite.trans (𝓞 E) Dw.La
  exact ⟨inferInstance, inferInstance⟩

theorem card_levQ_dvd {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} (Dw : Datum H)
    (l : Geo.Tor.Level H) : Nat.card (LevQ Dw l) ∣ l.M ^ Module.finrank ℤ Dw.La := by
  obtain ⟨hfree, hfin⟩ := datum_free Dw
  have hM : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb := by
    have h1 : ((l.M : ℕ) : 𝓞 E) ∈ Ideal.span {((l.M : ℕ) : 𝓞 E)} := Ideal.subset_span rfl
    rw [← l.prod] at h1
    exact (Ideal.mul_le_inf.trans inf_le_left) h1
  have hle : (nsmulAddMonoidHom (α := Dw.La) l.M).range ≤ (l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).toAddSubgroup := by
    rintro x ⟨y, rfl⟩
    simp only [nsmulAddMonoidHom_apply, Submodule.mem_toAddSubgroup]
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
    exact Submodule.smul_mem_smul hM Submodule.mem_top
  have key := AddSubgroup.index_dvd_of_le hle
  rw [AddSubgroup.index_range_nsmul] at key
  unfold LevQ
  exact key

private theorem relIndex_span_smul_stdLat {E : Type} [Field E] [NumberField E] {n : ℕ} (N : ℕ) :
    (Ideal.span {(N : 𝓞 E)} • Formalism.L2.Pj.stdLat E n).toAddSubgroup.relIndex
      (Formalism.L2.Pj.stdLat E n).toAddSubgroup = N ^ (Module.finrank ℚ E * n) := by
  have hmem : ∀ v : Fin n → E, v ∈ Formalism.L2.Pj.stdLat E n ↔ ∀ i, ∃ a : 𝓞 E, (a : E) = v i := by
    intro v
    simp only [Formalism.L2.Pj.stdLat, Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.mem_one]
  set L := (Formalism.L2.Pj.stdLat E n).toAddSubgroup with hL
  have hmap : (Ideal.span {(N : 𝓞 E)} • Formalism.L2.Pj.stdLat E n).toAddSubgroup =
      L.map (nsmulAddMonoidHom N) := by
    ext x
    simp only [Submodule.mem_toAddSubgroup, AddSubgroup.mem_map, nsmulAddMonoidHom_apply,
      Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists, hL]
    simp only [Nat.cast_smul_eq_nsmul]
  let g : (Fin n → 𝓞 E) →+ L :=
    { toFun := fun a => ⟨fun i => (a i : E), (hmem _).2 fun i => ⟨a i, rfl⟩⟩
      map_zero' := by ext; simp
      map_add' := by intro a b; ext; simp }
  have hg : Function.Bijective g := by
    constructor
    · intro a b hab
      funext i
      have := congrArg (fun v : L => (v : Fin n → E) i) hab
      exact RingOfIntegers.coe_injective this
    · rintro ⟨v, hv⟩
      choose a ha using (hmem v).1 hv
      exact ⟨a, Subtype.ext (funext ha)⟩
  let e : (Fin n → 𝓞 E) ≃ₗ[ℤ] L := (AddEquiv.ofBijective g hg).toIntLinearEquiv
  have : Module.Free ℤ L := Module.Free.of_equiv e
  have : Module.Finite ℤ L := Module.Finite.equiv e
  have hrank : Module.finrank ℤ L = Module.finrank ℚ E * n := by
    rw [← e.finrank_eq, Module.finrank_pi_fintype]
    simp [NumberField.RingOfIntegers.rank, mul_comm]
  rw [hmap, AddSubgroup.relIndex, AddSubgroup.addSubgroupOf_map_nsmulAddMonoidHom_eq_range,
    AddSubgroup.index_range_nsmul, hrank]

theorem relIndex_dvd {E : Type} [Field E] [NumberField E] {n : ℕ} (Λ : GenLat E n) (N : ℕ) (hN : 0 < N)
    (h : Ideal.span {(N : 𝓞 E)} • Formalism.L2.Pj.stdLat E n ≤ Λ.Ln) :
    (Ideal.span {(N : 𝓞 E)} • Formalism.L2.Pj.stdLat E n).toAddSubgroup.relIndex Λ.Ln.toAddSubgroup ∣ N ^ (Module.finrank ℚ E * n) := by
  have hHK : (Ideal.span {(N : 𝓞 E)} • Formalism.L2.Pj.stdLat E n).toAddSubgroup ≤ Λ.Ln.toAddSubgroup :=
    fun x hx => h hx
  have hKL : Λ.Ln.toAddSubgroup ≤ (Formalism.L2.Pj.stdLat E n).toAddSubgroup :=
    fun x hx => (inf_le_right : Λ.La ⊓ Formalism.L2.Pj.stdLat E n ≤ _) hx
  rw [← relIndex_span_smul_stdLat N]
  exact Dvd.intro _ (AddSubgroup.relIndex_mul_relIndex _ _ _ hHK hKL)

theorem mIdx_dvd {E : Type} [Field E] [NumberField E] {n : ℕ} (Λ : GenLat E n) (N r : ℕ) (hN : 0 < N)
    (h : Ideal.span {(N : 𝓞 E)} • Formalism.L2.Pj.stdLat E n ≤ Λ.Ln) : Λ.mIdx N r ∣ N ^ (Module.finrank ℚ E * n * r) := by
  have key := relIndex_dvd Λ N hN h
  rw [AddSubgroup.relIndex] at key
  rw [Formalism.L2.Pj.GenLat.mIdx, pow_mul]
  exact pow_dvd_pow_of_dvd key r

theorem const_dvd : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (n d M p : ℕ), p.Prime → M ≠ 0 → ∃ c : ℕ, ∀ (l₂ : Geo.Tor.Level H) (pd u : ℕ) (Λ : GenLat E n), l₂.M = M * pd → ¬ p ∣ pd → Nat.Coprime u p → Λ.LevOK (l₂.M * u) l₂.M → ∃ u' : ℕ, Nat.Coprime u' p ∧ ((Λ.mIdx (l₂.M * u) (Dw.p + Dw.q) * Nat.card (Fin n → LevQ Dw l₂) : ℕ) : ℤ) * (2 * NumberField.discr E * (l₂.M * u : ℕ)) ^ d ∣ ((p ^ c * u' : ℕ) : ℤ) := by
  intro E _ _ _ H Dw n d M p hp hM
  have hp1 : p ≠ 1 := hp.one_lt.ne'
  have hdisc : NumberField.discr E ≠ 0 := NumberField.discr_ne_zero E
  obtain ⟨K, hK⟩ : ∃ K : ℤ, K = (M : ℤ) ^ (Module.finrank ℚ E * n * (Dw.p + Dw.q)) *
      (M : ℤ) ^ (Module.finrank ℤ Dw.La * n) * (2 * NumberField.discr E * M) ^ d := ⟨_, rfl⟩
  have hK0 : K.natAbs ≠ 0 := by
    rw [Int.natAbs_ne_zero, hK]
    have hM' : (M : ℤ) ≠ 0 := by exact_mod_cast hM
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hM') (pow_ne_zero _ hM'))
      (pow_ne_zero _ (mul_ne_zero (mul_ne_zero two_ne_zero hdisc) hM'))
  obtain ⟨c, k, hk, hKk⟩ := Nat.exists_eq_pow_mul_and_not_dvd hK0 p hp1
  refine ⟨c, ?_⟩
  intro l₂ pd u Λ hl hpd hu hΛ
  have hu0 : u ≠ 0 := by
    rintro rfl
    exact hp1 (Nat.coprime_zero_left p |>.mp hu)
  have hN : 0 < l₂.M * u := Nat.mul_pos (by have := l₂.three_le; omega) (Nat.pos_of_ne_zero hu0)
  have h1 : Λ.mIdx (l₂.M * u) (Dw.p + Dw.q) ∣ (l₂.M * u) ^ (Module.finrank ℚ E * n * (Dw.p + Dw.q)) :=
    mIdx_dvd Λ _ _ hN hΛ.2.2
  have h2 : Nat.card (Fin n → LevQ Dw l₂) ∣ l₂.M ^ (Module.finrank ℤ Dw.La * n) := by
    rw [Nat.card_fun, Nat.card_fin, pow_mul]
    exact pow_dvd_pow_of_dvd (card_levQ_dvd Dw l₂) n
  have hcop : ∀ m : ℕ, ¬ p ∣ m → Nat.Coprime m p := fun m hm =>
    Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm)
  have hpd' := hcop pd hpd
  refine ⟨k * ((pd * u) ^ (Module.finrank ℚ E * n * (Dw.p + Dw.q)) * pd ^ (Module.finrank ℤ Dw.La * n) *
    (pd * u) ^ d), ?_, ?_⟩
  · exact Nat.Coprime.mul_left (hcop k hk) (Nat.Coprime.mul_left (Nat.Coprime.mul_left
      (Nat.Coprime.pow_left _ (Nat.Coprime.mul_left hpd' hu)) (Nat.Coprime.pow_left _ hpd'))
      (Nat.Coprime.pow_left _ (Nat.Coprime.mul_left hpd' hu)))
  · have hKd : K ∣ (K.natAbs : ℤ) := Int.dvd_natAbs.mpr dvd_rfl
    have h12 := Int.natCast_dvd_natCast.mpr (Nat.mul_dvd_mul h1 h2)
    have hprod : ((l₂.M * u : ℕ) : ℤ) ^ (Module.finrank ℚ E * n * (Dw.p + Dw.q)) * ((l₂.M : ℕ) : ℤ) ^ (Module.finrank ℤ Dw.La * n) *
        (2 * NumberField.discr E * ((l₂.M * u : ℕ) : ℤ)) ^ d =
        K * (((pd * u) ^ (Module.finrank ℚ E * n * (Dw.p + Dw.q)) * pd ^ (Module.finrank ℤ Dw.La * n) *
          (pd * u) ^ d : ℕ) : ℤ) := by
      rw [hK, hl]
      push_cast
      ring
    have hfin : ((p ^ c * (k * ((pd * u) ^ (Module.finrank ℚ E * n * (Dw.p + Dw.q)) * pd ^ (Module.finrank ℤ Dw.La * n) *
        (pd * u) ^ d)) : ℕ) : ℤ) = (K.natAbs : ℤ) * (((pd * u) ^ (Module.finrank ℚ E * n * (Dw.p + Dw.q)) *
          pd ^ (Module.finrank ℤ Dw.La * n) * (pd * u) ^ d : ℕ) : ℤ) := by
      rw [hKk]
      push_cast
      ring
    rw [hfin]
    refine dvd_trans ?_ (mul_dvd_mul_right hKd _)
    rw [← hprod]
    push_cast at h12 ⊢
    exact mul_dvd_mul h12 dvd_rfl

end GlobalTheory.ConstBound
