import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnChartAsm
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndex
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeVacuaExistUnique

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.ZLat

open GlobalTheory.SW.TensLat GlobalTheory.SW.TensVac

theorem exists_even_reps {G : Type} [AddCommGroup G] (A C : AddSubgroup G) {M : ℕ} (hM : Odd M)
    (hA : ∀ a ∈ A, M • a ∈ C) {c : ℕ} (hc : C.relIndex A = c) (h0 : c ≠ 0) :
    ∃ a : Fin c → G, (∀ i, a i ∈ A) ∧ (∀ i i', 2 • a i - 2 • a i' ∈ C → i = i') ∧
      ∀ y ∈ A, ∃ i, y - 2 • a i ∈ C := by
  obtain ⟨k, rfl⟩ := hM
  have hcard : Nat.card (A ⧸ C.addSubgroupOf A) = c := hc
  haveI : Finite (A ⧸ C.addSubgroupOf A) := Nat.finite_of_card_ne_zero (hcard ▸ h0)
  let e := (Finite.equivFinOfCardEq hcard).symm
  have key (x : A) : 2 • ((k + 1) • (x : G)) = x + (2 * k + 1) • (x : G) := by
    rw [smul_smul, show 2 * (k + 1) = (2 * k + 1) + 1 by ring, succ_nsmul, add_comm]
  refine ⟨fun i => (k + 1) • ((e i).out : A), fun i => A.nsmul_mem (e i).out.2 _, ?_, ?_⟩
  · intro i i' h
    apply e.injective
    rw [← QuotientAddGroup.out_eq' (e i), ← QuotientAddGroup.out_eq' (e i'), eq_comm,
      QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    rw [key, key] at h
    have := C.add_mem (C.sub_mem h (hA _ (e i).out.2)) (hA _ (e i').out.2)
    convert this using 1
    push_cast
    abel
  · intro y hy
    refine ⟨e.symm (⟨y, hy⟩ : A), ?_⟩
    rw [key, Equiv.apply_symm_apply]
    have h := QuotientAddGroup.out_eq' ((⟨y, hy⟩ : A) : A ⧸ C.addSubgroupOf A)
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at h
    have := C.sub_mem h (hA _ ((⟨y, hy⟩ : A) : A ⧸ C.addSubgroupOf A).out.2)
    convert this using 1
    push_cast
    abel

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ}

omit [IsCMField E] in
theorem stdLat_eq : stdLat E n = stdL E n := by
  ext x
  rw [Base.mem_stdL, stdLat, Submodule.mem_pi]
  refine forall_congr' fun k => ?_
  simp only [Set.mem_univ, true_imp_iff, Submodule.mem_one]
  exact ⟨fun ⟨a, ha⟩ => ha ▸ a.2, fun h => ⟨⟨_, h⟩, rfl⟩⟩

omit [IsCMField E] in
theorem mem_span_smul {N : ℕ} {S : Lt E n} {v : Fin n → E} :
    v ∈ Ideal.span {(N : 𝓞 E)} • S ↔ ∃ v' ∈ S, N • v' = v := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  simp only [Nat.cast_smul_eq_nsmul]

omit [IsCMField E] in
theorem vecMulVec_nsmul (N : ℕ) (v : Fin n → E) (u : Fin r → E) :
    vecMulVec (N • v) u = N • vecMulVec v u := by
  ext i j
  simp [vecMulVec_apply, _root_.mul_assoc]

omit [IsCMField E] in
theorem mem_tens_span_smul {N : ℕ} {S : Lt E n} {L : Lt E r} {y : Matrix (Fin n) (Fin r) E} :
    y ∈ tens (Ideal.span {(N : 𝓞 E)} • S) L ↔ ∃ z ∈ tens S L, N • z = y := by
  have : tens (Ideal.span {(N : 𝓞 E)} • S) L = (tens S L).map (nsmulAddMonoidHom N) := by
    apply le_antisymm
    · refine tens_le fun v hv u hu => ?_
      obtain ⟨v', hv', rfl⟩ := mem_span_smul.1 hv
      exact ⟨_, pure_mem hv' hu, (vecMulVec_nsmul N v' u).symm⟩
    · rw [AddSubgroup.map_le_iff_le_comap]
      refine tens_le fun v hv u hu => ?_
      rw [AddSubgroup.mem_comap, nsmulAddMonoidHom_apply, ← vecMulVec_nsmul]
      exact pure_mem (mem_span_smul.2 ⟨v, hv, rfl⟩) hu
  rw [this]
  rfl

theorem nsmul_mem_std {N : ℕ} {Λ : Lt E n} (hΛ : Λ ∈ Vset E n 1)
    (h : Ideal.span {(N : 𝓞 E)} • stdL E n ≤ Λ) {v : Fin n → E} (hv : v ∈ Λ) :
    N • v ∈ stdL E n := by
  rw [(Base.stdL_mem_Vset (E := E) n 1).2.1]
  intro y hy
  have := (hΛ.2.1 v).1 hv _ (h (mem_span_smul.2 ⟨y, hy, rfl⟩))
  convert this using 1
  simp only [Base.herm_one]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [cc]
  ring

variable {X : Data E r} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {w : E}
  {A B C : AddSubgroup (Matrix (Fin n) (Fin r) E)}

theorem sum_reps (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) (hn : Even n)
    (hA : Good X w A) (hCA : C ≤ A) (hCB : C ≤ B) {c : ℕ} (u : Fin c → Matrix (Fin n) (Fin r) E)
    (h1 : ∀ i, u i ∈ A) (h2 : ∀ i i', u i - u i' ∈ C → i = i') (h3 : ∀ y ∈ A, ∃ i, y - u i ∈ C)
    {v : TF n g} (hv : IsVac X bas w B v) :
    ∑ i, epsW X w (u i) • heisG X bas (u i) v = (c : ℂ) • projA X bas w A v := by
  obtain ⟨v', hv', -⟩ := hA.vac (bas := bas) hs
  have hsb (i) := rho_sb (w := w) idx hs hn (u i) hv.1
  have hsum (s : Finset (Fin c)) : IsSB (∑ i ∈ s, epsW X w (u i) • heisG X bas (u i) v) ∧
      SW.ip (∑ i ∈ s, epsW X w (u i) • heisG X bas (u i) v) v' = s.card * SW.ip v v' := by
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨isSB_zero, ?_⟩
      have := ip_smul_left 0 hv'.1 hv'.1
      simpa using this
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, ip_add_left (hsb a) ih.1 hv'.1, ih.2, Finset.card_insert_of_notMem ha]
      refine ⟨(GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ _ _ _ _ (hsb a) ih.1).1, ?_⟩
      have := rho_ip (w := w) idx hs hn (u a) hv.1 hv'.1
      rw [hv'.2.2 _ (h1 a)] at this
      rw [this]
      push_cast
      ring
  obtain ⟨k1, k2⟩ := hsum Finset.univ
  rw [hA.uniq hs hv' k1, k2, (hA.proj idx hs hn hv.1 hv').2, smul_smul, Finset.card_univ,
    Fintype.card_fin]
  intro y hy
  choose σ hσ using fun i => h3 (y + u i) (A.add_mem hy (h1 i))
  have hinj : Function.Injective σ := by
    intro i i' h
    apply h2
    have := C.sub_mem (hσ i) (hσ i')
    rw [h] at this
    convert this using 1
    abel
  have hlin (f : Fin c → SW.TF n g) : heisG X bas y (∑ i, f i) = ∑ i, heisG X bas y (f i) := by
    funext x; simp [heisG, heisS, Finset.sum_mul]
  rw [hlin, Finset.smul_sum]
  refine Fintype.sum_bijective σ (Finite.injective_iff_bijective.1 hinj) _ _ fun i => ?_
  rw [hA.rho_rho idx hs hn hy (h1 i) hv.1]
  conv_rhs => rw [← hv.2.2 _ (hCB (hσ i))]
  rw [hA.rho_rho idx hs hn (h1 _) (hCA (hσ i)) hv.1, add_sub_cancel]

end

theorem exists_reps_sum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : E, IsIntegral ℤ w → w + cc w = 1 → ∀ L : Lt E r, SelfD X L → ∀ Λ ∈ Vset E n 1, ∀ N : ℕ, Odd N → Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ → ∃ u : Fin ((⟨Λ⟩ : GenLat E n).zCard N r) → Matrix (Fin n) (Fin r) E, (∀ i, u i ∈ tens Λ L ∧ ∀ b, ∃ u' ∈ L, N • u i b = (2 : ℕ) • u') ∧ (∀ i i', (∀ b, ∃ u' ∈ L, u i b - u i' b = N • u') → i = i') ∧ 0 < (⟨Λ⟩ : GenLat E n).zCard N r ∧ 0 < (⟨Λ⟩ : GenLat E n).mIdx N r ∧ ∀ v : TF n g, IsVac X bas w (tens (stdL E n) L) v → ∑ i, heisG X bas (u i) v = (((⟨Λ⟩ : GenLat E n).zCard N r : ℕ) : ℂ) • projA X bas w (tens Λ L) v := by
  intro E _ _ _ r X g bas idx n hs hn w hw hw' L hL Λ hΛ N hN hle
  have hN0 : N ≠ 0 := hN.pos.ne'
  have hstd := Base.stdL_mem_Vset (E := E) n 1
  have hA : Good X w (tens Λ L) := by
    obtain ⟨h1, h2, h3, -⟩ :=
      tens_selfDual_semichar_index E r X g bas idx n hs hn w hw hw' L hL 1 Λ hΛ
    exact ⟨h1, h2, h3⟩
  have hle' := hle
  rw [stdLat_eq] at hle'
  have hsp : Submodule.span E ((Ideal.span {(N : 𝓞 E)} • stdL E n : Lt E n) : Set (Fin n → E)) = ⊤ := by
    rw [eq_top_iff, ← DualFamily.span_eq_top _ hstd.1 fun x => (hstd.2.1 x).2, Submodule.span_le]
    intro x hx
    have : x = (N : E)⁻¹ • (N • x) := by
      rw [← Nat.cast_smul_eq_nsmul E, inv_smul_smul₀ (Nat.cast_ne_zero.2 hN0)]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (mem_span_smul.2 ⟨x, hx, rfl⟩))
  have hidx : (tens (Ideal.span {(N : 𝓞 E)} • stdL E n) L).relIndex (tens Λ L) =
      (⟨Λ⟩ : GenLat E n).zCard N r := by
    rw [relIndex_tens_left hL.1 (span_of_selfD X hL) hΛ.1 hsp, GenLat.zCard, stdLat_eq]
    rfl
  have hfin : (Ideal.span {(N : 𝓞 E)} • stdLat E n).toAddSubgroup.relIndex Λ.toAddSubgroup ≠ 0 := by
    have hfg : Λ.toAddSubgroup.FG := by
      haveI : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.2 hΛ.1
      haveI : Module.Finite ℤ Λ := Module.Finite.trans (𝓞 E) Λ
      exact (AddGroup.fg_iff_addSubgroup_fg _).1 (Module.Finite.iff_addGroup_fg.1 this)
    haveI : AddGroup.FG Λ.toAddSubgroup := (AddGroup.fg_iff_addSubgroup_fg _).2 hfg
    haveI := AddSubgroup.finiteIndex_range_nsmulAddMonoidHom_of_fg Λ.toAddSubgroup
      (mul_ne_zero hN0 hN0)
    have : (nsmulAddMonoidHom (α := Λ.toAddSubgroup) (N * N)).range ≤
        (Ideal.span {(N : 𝓞 E)} • stdLat E n).toAddSubgroup.addSubgroupOf Λ.toAddSubgroup := by
      rintro _ ⟨x, rfl⟩
      rw [AddSubgroup.mem_addSubgroupOf, Submodule.mem_toAddSubgroup, stdLat_eq, mem_span_smul]
      exact ⟨N • (x : Fin n → E), nsmul_mem_std hΛ hle' x.2, by simp [mul_smul]⟩
    exact (AddSubgroup.finiteIndex_of_le this).index_ne_zero
  have hz : 0 < (⟨Λ⟩ : GenLat E n).zCard N r := pow_pos (Nat.pos_of_ne_zero hfin) r
  have hm : 0 < (⟨Λ⟩ : GenLat E n).mIdx N r := by
    refine pow_pos (Nat.pos_of_ne_zero fun h => hfin ?_) r
    exact AddSubgroup.relIndex_eq_zero_of_le_right (K := (⟨Λ⟩ : GenLat E n).Ln.toAddSubgroup)
      (fun x hx => hx.1) h
  have hNA : ∀ y ∈ tens Λ L, N • y ∈ tens (stdL E n) L := by
    have : tens Λ L ≤ (tens (stdL E n) L).comap (nsmulAddMonoidHom N) :=
      tens_le fun v hv u hu => by
        rw [AddSubgroup.mem_comap, nsmulAddMonoidHom_apply, ← vecMulVec_nsmul]
        exact pure_mem (nsmul_mem_std hΛ hle' hv) hu
    exact fun y hy => this hy
  obtain ⟨a, ha1, ha2, ha3⟩ := exists_even_reps (tens Λ L)
    (tens (Ideal.span {(N : 𝓞 E)} • stdL E n) L) (hN.mul hN)
    (fun y hy => mem_tens_span_smul.2 ⟨_, hNA y hy, by rw [mul_smul]⟩) hidx hz.ne'
  refine ⟨fun i => 2 • a i, fun i => ⟨AddSubgroup.nsmul_mem _ (ha1 i) 2, fun b =>
    ⟨_, (mem_tens_stdL L _).1 (hNA _ (ha1 i)) b, ?_⟩⟩, fun i i' h => ha2 i i' ?_, hz, hm,
    fun v hv => ?_⟩
  · exact smul_comm N 2 (a i b)
  · choose z hz hz' using h
    refine mem_tens_span_smul.2 ⟨z, (mem_tens_stdL L _).2 hz, ?_⟩
    funext b
    exact (hz' b).symm
  · rw [← sum_reps idx hs hn hA (C := tens (Ideal.span {(N : 𝓞 E)} • stdL E n) L)
      (tens_le fun v hv u hu => pure_mem (hle' hv) hu)
      (tens_le fun v hv u hu => pure_mem (Submodule.smul_le_right hv) hu)
      (fun i => 2 • a i) (fun i => AddSubgroup.nsmul_mem _ (ha1 i) 2) ha2 ha3 hv]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hA.eps_two hs (ha1 i), one_smul]

end GlobalTheory.Dict.ZLat
