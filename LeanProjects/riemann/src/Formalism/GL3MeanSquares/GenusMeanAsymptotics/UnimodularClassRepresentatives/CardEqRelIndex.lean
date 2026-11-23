import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AbsNormDiscrIdealOfLe
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FinrankRingOfIntegers
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.VdEqZeroOfNotLe
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsMulDvdUnif

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.LIOrb.IA

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

def mu (𝔮 I : Ideal (𝓞 F)) : ℕ := sSup {e : ℕ | I ≤ 𝔮 ^ e}

theorem mu_mul {𝔮 : Ideal (𝓞 F)} (h𝔮 : 𝔮.IsMaximal) {I J : Ideal (𝓞 F)} (hI : I ≠ ⊥)
    (hJ : J ≠ ⊥) : mu 𝔮 (I * J) = mu 𝔮 I + mu 𝔮 J := by
  let v := BrA.maxEquiv F ⟨𝔮, h𝔮⟩
  have hIJ : I * J ≠ ⊥ := mul_ne_zero hI hJ
  have e : ∀ X : Ideal (𝓞 F), X ≠ ⊥ → mu 𝔮 X = multiplicity v.asIdeal X :=
    fun X hX => BrA.sSup_le_pow v hX
  rw [e _ hIJ, e _ hI, e _ hJ]
  exact multiplicity_mul v.prime (FiniteMultiplicity.of_not_isUnit v.prime.not_isUnit hIJ)

theorem discrIdeal_mono {h : V →ₗ⋆[K] V →ₗ[K] K} {A B : Submodule (𝓞 K) V} (hAB : A ≤ B) :
    discrIdeal h A ≤ discrIdeal h B := by
  unfold discrIdeal
  apply Ideal.span_mono
  rintro z ⟨x, hx, e⟩
  exact ⟨x, fun i => hAB (hx i), e⟩

theorem exists_pow_smul {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {M N : Submodule (𝓞 K) V}
    (hM : Submodule.IsLattice K M) (hN : Submodule.IsLattice K N) :
    ∃ r : ℕ, ∀ a ∈ 𝔭 ^ r, ∀ y ∈ M, ι a • y ∈ locF 𝔭 N := by
  have hp := h𝔭.isPrime
  obtain ⟨n, hn, hnx⟩ := LocF.exists_zsmul_le hM hN
  have hn' : (n : 𝓞 F) ≠ 0 := by exact_mod_cast hn
  obtain ⟨r, u, hu, hdvd⟩ := D2.exists_mul_dvd h𝔭 hn'
  refine ⟨r, fun a ha y hy => ?_⟩
  rw [LocF.mem_locF_iff hp]
  refine ⟨u, hu, ?_⟩
  obtain ⟨d, hd⟩ := hdvd a ha
  rw [smul_smul, ← map_mul, hd, map_mul, mul_comm, mul_smul, LocF.algebraMap_intCast_smul]
  exact N.smul_mem _ (hnx y hy)

theorem mem_locF_of_smul {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsPrime) {N : Submodule (𝓞 K) V} {t : 𝓞 F}
    (ht : t ∉ 𝔭) {x : V} (hx : ι t • x ∈ locF 𝔭 N) : x ∈ locF 𝔭 N := by
  obtain ⟨s, hs, h⟩ := (LocF.mem_locF_iff hp N _).1 hx
  refine (LocF.mem_locF_iff hp N x).2 ⟨s * t, fun hm => (hp.mem_or_mem hm).elim hs ht, ?_⟩
  rwa [map_mul, mul_smul]

theorem pow_smul_locF {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {M N : Submodule (𝓞 K) V} {r : ℕ}
    (hr : ∀ a ∈ 𝔭 ^ r, ∀ y ∈ M, ι a • y ∈ locF 𝔭 N) {a : 𝓞 F} (ha : a ∈ 𝔭 ^ r) {x : V}
    (hx : x ∈ locF 𝔭 M) : ι a • x ∈ locF 𝔭 N := by
  obtain ⟨t, ht, htx⟩ := (LocF.mem_locF_iff h𝔭.isPrime M x).1 hx
  apply mem_locF_of_smul h𝔭.isPrime ht
  rw [smul_comm]
  exact hr a ha _ htx

theorem locF_inf_of_ne {𝔭 𝔮 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (h𝔮 : 𝔮.IsMaximal) (hne : 𝔮 ≠ 𝔭)
    {M N : Submodule (𝓞 K) V} {r : ℕ} (hr : ∀ a ∈ 𝔭 ^ r, ∀ y ∈ M, ι a • y ∈ locF 𝔭 N) :
    locF 𝔮 (M ⊓ locF 𝔭 N) = locF 𝔮 M := by
  apply le_antisymm (LocF.locF_mono 𝔮 inf_le_left)
  have hnle : ¬ 𝔭 ^ r ≤ 𝔮 := fun hle =>
    hne (h𝔭.eq_of_le h𝔮.ne_top (h𝔮.isPrime.le_of_pow_le hle)).symm
  obtain ⟨a, ha, ha𝔮⟩ := SetLike.not_le_iff_exists.mp hnle
  have hM : M ≤ locF 𝔮 (M ⊓ locF 𝔭 N) := by
    intro y hy
    exact (LocF.mem_locF_iff h𝔮.isPrime _ y).2
      ⟨a, ha𝔮, Submodule.mem_inf.2 ⟨M.smul_mem _ hy, hr a ha y hy⟩⟩
  calc locF 𝔮 M ≤ locF 𝔮 (locF 𝔮 (M ⊓ locF 𝔭 N)) := LocF.locF_mono 𝔮 hM
    _ = _ := LocF.locF_idem 𝔮 _

theorem locF_inf (𝔭 : Ideal (𝓞 F)) (hp : 𝔭.IsPrime) (M N : Submodule (𝓞 K) V) :
    locF 𝔭 (M ⊓ locF 𝔭 N) = locF 𝔭 M ⊓ locF 𝔭 N := by
  apply le_antisymm
  · refine le_inf (LocF.locF_mono 𝔭 inf_le_left) ?_
    calc locF 𝔭 (M ⊓ locF 𝔭 N) ≤ locF 𝔭 (locF 𝔭 N) := LocF.locF_mono 𝔭 inf_le_right
      _ = locF 𝔭 N := LocF.locF_idem 𝔭 N
  · intro x hx
    obtain ⟨t, ht, htx⟩ := (LocF.mem_locF_iff hp M x).1 (Submodule.mem_inf.1 hx).1
    exact (LocF.mem_locF_iff hp _ x).2 ⟨t, ht, Submodule.mem_inf.2
      ⟨htx, (locF 𝔭 N).smul_mem _ (Submodule.mem_inf.1 hx).2⟩⟩

theorem card_eq_relIndex {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {M N : Submodule (𝓞 K) V} {r : ℕ}
    (hr : ∀ a ∈ 𝔭 ^ r, ∀ y ∈ M, ι a • y ∈ locF 𝔭 N) :
    Nat.card (↥(locF 𝔭 M) ⧸ (locF 𝔭 M ⊓ locF 𝔭 N).submoduleOf (locF 𝔭 M)) =
      (M ⊓ locF 𝔭 N).toAddSubgroup.relIndex M.toAddSubgroup := by
  set B' := (locF 𝔭 M ⊓ locF 𝔭 N).submoduleOf (locF 𝔭 M) with hB'
  let φ : ↥M →ₗ[𝓞 K] ↥(locF 𝔭 M) ⧸ B' := B'.mkQ ∘ₗ Submodule.inclusion (LocF.le_locF 𝔭 M)
  have hsurj : Function.Surjective φ := by
    intro z
    induction z using Submodule.Quotient.induction_on with
    | H x =>
    obtain ⟨c, hc, hcx⟩ := localizedQuotients.exists_approx h𝔭 M r x.2
    refine ⟨⟨_, hcx⟩, ?_⟩
    simp only [φ, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply]
    rw [Submodule.Quotient.eq]
    change (ι c • (x : V) - (x : V)) ∈ locF 𝔭 M ⊓ locF 𝔭 N
    have e : ι c • (x : V) - (x : V) = ι (c - 1) • (x : V) := by
      rw [map_sub, map_one, sub_smul, one_smul]
    rw [e]
    exact Submodule.mem_inf.2 ⟨(locF 𝔭 M).smul_mem _ x.2, pow_smul_locF h𝔭 hr hc x.2⟩
  have hker : (LinearMap.ker φ).toAddSubgroup =
      (M ⊓ locF 𝔭 N).toAddSubgroup.addSubgroupOf M.toAddSubgroup := by
    ext y
    rw [AddSubgroup.mem_addSubgroupOf, Submodule.mem_toAddSubgroup, LinearMap.mem_ker]
    simp only [φ, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    change ((y : V) ∈ locF 𝔭 M ⊓ locF 𝔭 N) ↔ (y : V) ∈ M ⊓ locF 𝔭 N
    rw [Submodule.mem_inf, Submodule.mem_inf]
    exact ⟨fun h => ⟨y.2, h.2⟩, fun h => ⟨LocF.le_locF 𝔭 M y.2, h.2⟩⟩
  rw [AddSubgroup.relIndex, AddSubgroup.index, ← hker]
  exact (Nat.card_congr (φ.quotKerEquivOfSurjective hsurj).toEquiv).symm

theorem relIndex_ne_zero {M N : Submodule (𝓞 K) V} (hM : Submodule.IsLattice K M)
    (hN : Submodule.IsLattice K N) (𝔭 : Ideal (𝓞 F)) :
    (M ⊓ locF 𝔭 N).toAddSubgroup.relIndex M.toAddSubgroup ≠ 0 := by
  obtain ⟨n, hn, hnx⟩ := LocF.exists_zsmul_le hM hN
  have f1 : Module.Finite (𝓞 K) M := Module.Finite.iff_fg.mpr hM.fg
  have f2 : Module.Finite ℤ M := Module.Finite.trans (𝓞 K) M
  have f3 : AddGroup.FG M.toAddSubgroup := Module.Finite.iff_addGroup_fg.mp f2
  have : Finite (↥M.toAddSubgroup ⧸ (M ⊓ locF 𝔭 N).toAddSubgroup.addSubgroupOf M.toAddSubgroup) := by
    apply AddCommGroup.finite_of_fg_isAddTorsion
    intro x
    induction x using QuotientAddGroup.induction_on with
    | H q =>
      rw [isOfFinAddOrder_iff_zsmul_eq_zero]
      refine ⟨n, hn, ?_⟩
      rw [← QuotientAddGroup.mk_zsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
      exact Submodule.mem_inf.2 ⟨zsmul_mem q.2 n, LocF.le_locF 𝔭 N (hnx _ q.2)⟩
  exact AddSubgroup.index_ne_zero_of_finite

theorem vd_mul {𝔭 : Ideal (𝓞 F)} (hF : IsFixF K F) [FiniteDimensional K V] (hK : Formalism.HermitianLatticesTheory.IsCMUnram K)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h)
    {M N : Submodule (𝓞 K) V} (hM : Submodule.IsLattice K M) (hMi : Formalism.HermitianLatticesTheory.IsIntegralLat h M)
    (hN : Submodule.IsLattice K N) (h𝔭 : 𝔭.IsMaximal) :
    (M ⊓ locF 𝔭 N).toAddSubgroup.relIndex M.toAddSubgroup * Ideal.absNorm 𝔭 ^ vd h M 𝔭 =
      Ideal.absNorm 𝔭 ^ vd h (M ⊓ locF 𝔭 N) 𝔭 := by
  set M'' := M ⊓ locF 𝔭 N with hM''
  set n := M''.toAddSubgroup.relIndex M.toAddSubgroup with hn
  have hn0 : n ≠ 0 := relIndex_ne_zero hM hN 𝔭
  obtain ⟨r, hr⟩ := exists_pow_smul h𝔭 hM hN
  have hle : M'' ≤ M := inf_le_left
  have hnorm := BallB.absNorm_discrIdeal_of_le hK hMi (Module.finBasis K V) n M'' hle rfl hn0
  rw [BrA.discrIdeal_eq_map hF hs M'', BrA.discrIdeal_eq_map hF hs M, BrA.absNorm_map hK hF,
    BrA.absNorm_map hK hF, ← mul_pow] at hnorm
  have hnorm' : Ideal.absNorm (BrA.discrF F h M'') = n * Ideal.absNorm (BrA.discrF F h M) :=
    Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) hnorm
  have hD : BrA.discrF F h M ≠ ⊥ := by
    intro hb
    apply LocF.discrIdeal_ne_bot (LocF.aniso_of_totPosDef hd) hM hMi
    rw [BrA.discrIdeal_eq_map hF hs M, hb, Ideal.map_bot]
  have hdvd : BrA.discrF F h M ∣ BrA.discrF F h M'' := by
    rw [Ideal.dvd_iff_le]
    exact Ideal.comap_mono (discrIdeal_mono hle)
  obtain ⟨J, hJ⟩ := hdvd
  have hDn : Ideal.absNorm (BrA.discrF F h M) ≠ 0 := by
    rwa [Ne, Ideal.absNorm_eq_zero_iff]
  have hJn : Ideal.absNorm J = n := by
    rw [hJ, map_mul, mul_comm] at hnorm'
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hDn) hnorm'
  have hJ0 : J ≠ ⊥ := by
    intro hb
    rw [hb, Ideal.absNorm_bot] at hJn
    exact hn0 hJn.symm
  have hother : ∀ 𝔮 : {𝔮 : Ideal (𝓞 F) // 𝔮.IsMaximal}, 𝔮.1 ≠ 𝔭 → mu 𝔮.1 J = 0 := by
    intro 𝔮 hne
    have e1 : vd h M'' 𝔮.1 = vd h M 𝔮.1 := by
      rw [← localizedQuotients.vd_locF hF h M'' 𝔮.2, hM'', locF_inf_of_ne h𝔭 𝔮.2 hne hr, localizedQuotients.vd_locF hF h M 𝔮.2]
    rw [BrA.vd_eq hF hs M'', BrA.vd_eq hF hs M, hJ] at e1
    change mu 𝔮.1 (_ * J) = mu 𝔮.1 _ at e1
    rw [mu_mul 𝔮.2 hD hJ0] at e1
    omega
  have hJn' : Ideal.absNorm J = Ideal.absNorm 𝔭 ^ mu 𝔭 J := by
    have := BrA.absNorm_eq_tprod hJ0
    rw [tprod_eq_mulSingle ⟨𝔭, h𝔭⟩] at this
    · have h3 : (Ideal.absNorm J : ℝ) = ((Ideal.absNorm 𝔭 ^ mu 𝔭 J : ℕ) : ℝ) := by
        rw [Nat.cast_pow]; exact this
      exact_mod_cast h3
    · intro 𝔮 hne
      rw [show sSup {e : ℕ | J ≤ 𝔮.1 ^ e} = mu 𝔮.1 J from rfl,
        hother 𝔮 (fun h => hne (Subtype.ext h)), pow_zero]
  have hvd : vd h M'' 𝔭 = vd h M 𝔭 + mu 𝔭 J := by
    rw [BrA.vd_eq hF hs M'', BrA.vd_eq hF hs M, hJ]
    exact mu_mul h𝔭 hD hJ0
  rw [hvd, pow_add, ← hJn', hJn, mul_comm]

end Formalism.HermitianLattices.Ext.L3.LIOrb.IA
