import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLatIntVec

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.DeltaIndex

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

variable {K : Type} [Field K] [NumberField K] {m : ℕ}

theorem delta_ne_zero (c : Matrix (Fin m) (Fin m) K) : delta c ≠ 0 := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 K))
    (Finset.univ : Finset (Fin m × Fin m)) (fun p => c p.1 p.2)
  have hb0 : (b : 𝓞 K) ≠ 0 := nonZeroDivisors.ne_zero b.2
  choose r hr using fun (i j : Fin m) => RingHom.mem_rangeS.1 (hb (i, j) (Finset.mem_univ _))
  have hr' : ∀ i j, algebraMap (𝓞 K) K (r i j) = algebraMap (𝓞 K) K (b : 𝓞 K) * c i j := by
    intro i j
    rw [hr i j, Algebra.smul_def]
  let I : Ideal (𝓞 K) := Ideal.span {(b : 𝓞 K)}
  have hI : I ≠ ⊥ := fun h => hb0 (Ideal.span_singleton_eq_bot.1 h)
  haveI : Finite (𝓞 K ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hI
  let π : (Fin m → 𝓞 K) →+ (Fin m → 𝓞 K ⧸ I) :=
    AddMonoidHom.pi (fun i => (Ideal.Quotient.mk I).toAddMonoidHom.comp
      (Pi.evalAddMonoidHom (fun _ : Fin m => 𝓞 K) i))
  have hker : π.ker ≤ Kc c := by
    intro y hy
    have h0 : π y = 0 := AddMonoidHom.mem_ker.1 hy
    have hyI : ∀ j, y j ∈ I := fun j =>
      Ideal.Quotient.eq_zero_iff_mem.1 (congrFun h0 j)
    choose z hz using fun j => Ideal.mem_span_singleton'.1 (hyI j)
    change ∀ i : Fin m, ∃ o : 𝓞 K,
      algebraMap (𝓞 K) K o = c.mulVec (fun j => algebraMap (𝓞 K) K (y j)) i
    intro i
    refine ⟨∑ j, r i j * z j, ?_⟩
    rw [map_sum]
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [map_mul, hr' i j, ← hz j, map_mul]
    ring
  have hfin : (π.ker).index ≠ 0 := by
    rw [AddSubgroup.index_ker]
    exact Nat.card_pos.ne'
  exact ne_zero_of_dvd_ne_zero hfin (AddSubgroup.index_dvd_of_le hker)

theorem delta_eq_relIndex (c : Matrix (Fin m) (Fin m) K) :
    delta c = (intVec K m).toAddSubgroup.relIndex (lam c).toAddSubgroup := by
  classical
  let L := (lam c).toAddSubgroup
  let H : AddSubgroup L := (intVec K m).toAddSubgroup.addSubgroupOf L
  let f0 : (Fin m → 𝓞 K) →+ (Fin m → K) :=
    (c.mulVecLin.toAddMonoidHom).comp (AddMonoidHom.pi fun i =>
      (algebraMap (𝓞 K) K).toAddMonoidHom.comp (Pi.evalAddMonoidHom (fun _ : Fin m => 𝓞 K) i))
  have hmap : ∀ y, f0 y ∈ L := by
    intro y
    have : f0 y ∈ lam c := by
      unfold lam
      refine Submodule.mem_sup_right (Submodule.mem_map.2 ⟨fun j => algebraMap (𝓞 K) K (y j),
        fun j => ⟨y j, rfl⟩, rfl⟩)
    exact this
  let ψ : (Fin m → 𝓞 K) →+ L := f0.codRestrict L hmap
  let φ : (Fin m → 𝓞 K) →+ L ⧸ H := (QuotientAddGroup.mk' H).comp ψ
  have hker : Kc c = φ.ker := by
    ext y
    rw [AddMonoidHom.mem_ker]
    change _ ↔ (QuotientAddGroup.mk (ψ y) : L ⧸ H) = 0
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    rfl
  have hsurj : Function.Surjective φ := by
    intro q
    induction q using QuotientAddGroup.induction_on with
    | H x =>
      obtain ⟨x, hx⟩ := x
      have hx' : x ∈ lam c := hx
      unfold lam at hx'
      obtain ⟨a, ha, w, hw, rfl⟩ := Submodule.mem_sup.1 hx'
      obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.1 hw
      choose y hy using hv
      refine ⟨y, ?_⟩
      have hyv : (fun j => algebraMap (𝓞 K) K (y j)) = v := funext hy
      change (QuotientAddGroup.mk (ψ y) : L ⧸ H) = QuotientAddGroup.mk _
      rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
      have key : ((-(ψ y) + ⟨_, hx⟩ : L) : Fin m → K) = a := by
        rw [AddSubgroup.coe_add, AddSubgroup.coe_neg]
        change -(c.mulVec (fun j => algebraMap (𝓞 K) K (y j))) + (a + c.mulVec v) = a
        rw [hyv]
        abel
      rw [key]
      exact ha
  show (Kc c).index = H.index
  rw [hker, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hsurj, AddSubgroup.card_top]
  rfl

theorem delta_index : ∀ (K : Type) [Field K] [NumberField K] (m : ℕ)
    (c : Matrix (Fin m) (Fin m) K),
    delta c ≠ 0 ∧ delta c = (intVec K m).toAddSubgroup.relIndex (lam c).toAddSubgroup := by
  intro K _ _ m c
  exact ⟨delta_ne_zero c, delta_eq_relIndex c⟩

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.DeltaIndex
