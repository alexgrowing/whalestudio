import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BlockSplitAll
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsobaricDiscreteSelfDualStrongMultiplicityOne
import Formalism.LocalToGlobal.GaloisLevelStructure.TiedHecke
import Formalism.LocalToGlobal.NormalizedHeckeFactors.HeckeStdTwOfStd
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverAct
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ResidueEqOfGenerators
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

noncomputable section

namespace GlobalTheory.PtLocalEig

theorem residue_map_equiv {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R']
    (φ : R ≃+* R') {a b : R} (h : IsLocalRing.residue R a = IsLocalRing.residue R b) :
    IsLocalRing.residue R' (φ a) = IsLocalRing.residue R' (φ b) := by
  have h' : IsLocalRing.residue R (a - b) = 0 := by rw [map_sub, h, sub_self]
  rw [IsLocalRing.residue_eq_zero_iff] at h'
  rw [← sub_eq_zero, ← map_sub, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  refine (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 fun hu => ?_)
  exact mem_nonunits_iff.1 ((IsLocalRing.mem_maximalIdeal _).1 h') ((isUnit_map_iff φ _).1 hu)

theorem heckeD_add (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) {W : Type} [AddCommGroup W]
    [Module ℂ W] (J : Subgroup (Formalism.AUTREP.GAf L n)) (Dset : Set (Formalism.AUTREP.GAf L n))
    (hfin : ((fun x : Formalism.AUTREP.GAf L n => (x : Formalism.AUTREP.GAf L n ⧸ J)) '' Dset).Finite)
    (c : ℂ) (f f' : Formalism.AUTREP.GAf L n → W) :
    Formalism.L2.NG.heckeD J Dset (c • f + f') = c • Formalism.L2.NG.heckeD J Dset f + Formalism.L2.NG.heckeD J Dset f' := by
  classical
  funext g
  have hsub : ∀ F : Formalism.AUTREP.GAf L n → W,
      Function.support (fun cc : Formalism.AUTREP.GAf L n ⧸ J =>
        if hc : ∃ x ∈ Dset, (x : Formalism.AUTREP.GAf L n ⧸ J) = cc then F (g * hc.choose) else 0) ⊆
        (hfin.toFinset : Set (Formalism.AUTREP.GAf L n ⧸ J)) := by
    intro F cc hcc
    rw [Set.Finite.coe_toFinset]
    by_contra hn
    apply hcc
    dsimp only
    rw [dif_neg]
    rintro ⟨x, hx, rfl⟩
    exact hn ⟨x, hx, rfl⟩
  rw [Pi.add_apply, Pi.smul_apply]
  simp only [Formalism.L2.NG.heckeD]
  rw [finsum_eq_sum_of_support_subset _ (hsub _), finsum_eq_sum_of_support_subset _ (hsub _),
    finsum_eq_sum_of_support_subset _ (hsub _), Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun cc _ => ?_
  split_ifs <;> simp

theorem cls_eq_of_residue : ∀ {O K V : Type} [CommRing O] [Field K] [Algebra O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] [IsLocalRing O] (S : Set (Module.End K V)) (ψ ψ' : Algebra.adjoin O S →ₐ[O] O), (∀ a (h : a ∈ S), IsLocalRing.residue O (ψ ⟨a, Algebra.subset_adjoin h⟩) = IsLocalRing.residue O (ψ' ⟨a, Algebra.subset_adjoin h⟩)) → Formalism.L2.NCov.cls ψ = Formalism.L2.NCov.cls ψ' := by
  first
  | exact @_root_.GlobalTheory.ClassResidueGenerators.cls_eq_of_generators
  | exact _root_.GlobalTheory.ClassResidueGenerators.cls_eq_of_generators
  | (apply _root_.GlobalTheory.ClassResidueGenerators.cls_eq_of_generators <;> assumption)
  | (intros; apply _root_.GlobalTheory.ClassResidueGenerators.cls_eq_of_generators <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ClassResidueGenerators.cls_eq_of_generators <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ClassResidueGenerators.cls_eq_of_generators ..)

theorem pt_of_eigvec : ∀ {O K V : Type} [CommRing O] [Field K] [Algebra O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] (S : Set (Module.End K V)) (e : V), e ≠ 0 → Function.Injective (algebraMap O K) → (∀ a ∈ S, ∃ c : O, a e = algebraMap O K c • e) → ∃ ψ : Algebra.adjoin O S →ₐ[O] O, (∀ t : Algebra.adjoin O S, (t : Module.End K V) e = algebraMap O K (ψ t) • e) ∧ e ∈ Formalism.L2.NCov.W (Algebra.adjoin O S) (Formalism.L2.NCov.pt ψ) := by
  intro O K V _ _ _ _ _ _ _ S e he hinj hS
  have key : ∀ t ∈ Algebra.adjoin O S, ∃ c : O, t e = algebraMap O K c • e := by
    intro t ht
    induction ht using Algebra.adjoin_induction with
    | mem a ha => exact hS a ha
    | algebraMap r => exact ⟨r, by rw [Formalism.L2.NCov.algebraMap_end_eq]; simp⟩
    | add a b _ _ iha ihb =>
      obtain ⟨c1, h1⟩ := iha
      obtain ⟨c2, h2⟩ := ihb
      exact ⟨c1 + c2, by rw [LinearMap.add_apply, h1, h2, map_add, add_smul]⟩
    | mul a b _ _ iha ihb =>
      obtain ⟨c1, h1⟩ := iha
      obtain ⟨c2, h2⟩ := ihb
      exact ⟨c1 * c2, by rw [Module.End.mul_apply, h2, map_smul, h1, smul_smul, map_mul, mul_comm]⟩
  choose f hf using fun t : Algebra.adjoin O S => key t t.2
  have uniq : ∀ c c' : O, algebraMap O K c • e = algebraMap O K c' • e → c = c' :=
    fun c c' hcc => hinj (smul_left_injective K he hcc)
  have f1 : f 1 = 1 := uniq _ _ (by rw [← hf 1, map_one, one_smul]; rfl)
  have fm : ∀ s t, f (s * t) = f s * f t := fun s t => uniq _ _ (by
    rw [← hf (s * t), map_mul, mul_comm, mul_smul, ← hf s, ← map_smul, ← hf t]; rfl)
  have f0 : f 0 = 0 := uniq _ _ (by rw [← hf 0, map_zero, zero_smul]; rfl)
  have fa : ∀ s t, f (s + t) = f s + f t := fun s t => uniq _ _ (by
    rw [← hf (s + t), map_add, add_smul, ← hf s, ← hf t]; rfl)
  have fc : ∀ r, f (algebraMap O (Algebra.adjoin O S) r) = r := fun r => uniq _ _ (by
    rw [← hf]
    show (algebraMap O (Module.End K V) r) e = _
    rw [Formalism.L2.NCov.algebraMap_end_eq]; simp)
  let ψ : Algebra.adjoin O S →ₐ[O] O :=
    { toFun := f, map_one' := f1, map_mul' := fm, map_zero' := f0, map_add' := fa, commutes' := fc }
  refine ⟨ψ, fun t => hf t, ?_⟩
  refine (Submodule.mem_iInf _).2 fun t => ?_
  rw [Module.End.mem_maxGenEigenspace]
  refine ⟨1, ?_⟩
  simp only [pow_one, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, Formalism.L2.NCov.pt]
  rw [hf t]
  exact sub_self _

theorem descent : ∀ {K C : Type} [Field K] [Field C] (φ : K →+* C) {ι : Type} [Fintype ι] {G : Type} (Mg : G → Matrix ι ι K) (d : ι → C), d ≠ 0 → (∀ g, Matrix.mulVec ((Mg g).map φ) d = 0) → ∃ c : ι → K, c ≠ 0 ∧ ∀ g, Matrix.mulVec (Mg g) c = 0 := by
  intro K C _ _ φ ι _ G Mg d hd hdg
  classical
  by_contra hne
  push_neg at hne
  let kerS : Finset G → Submodule K (ι → K) := fun s => ⨅ g ∈ s, LinearMap.ker (Matrix.mulVecLin (Mg g))
  have hex : ∃ m, ∃ s : Finset G, Module.finrank K (kerS s) = m := ⟨_, ∅, rfl⟩
  obtain ⟨s, hs⟩ := Nat.find_spec hex
  have hmin : ∀ s' : Finset G, Module.finrank K (kerS s) ≤ Module.finrank K (kerS s') := fun s' =>
    hs ▸ Nat.find_min' hex ⟨s', rfl⟩
  have hbot : kerS s = ⊥ := by
    rw [eq_bot_iff]
    intro c hc
    rw [Submodule.mem_bot]
    by_contra hc0
    obtain ⟨g, hg⟩ := hne c hc0
    have hins : kerS (insert g s) = LinearMap.ker (Matrix.mulVecLin (Mg g)) ⊓ kerS s := by
      simp only [kerS, Finset.iInf_insert]
    have hle : kerS (insert g s) ≤ kerS s := by rw [hins]; exact inf_le_right
    have heq := Submodule.eq_of_le_of_finrank_le hle (hmin _)
    have hc' : c ∈ kerS (insert g s) := heq ▸ hc
    rw [hins] at hc'
    exact hg (LinearMap.mem_ker.1 (Submodule.mem_inf.1 hc').1)
  let R : Matrix (↥s × ι) ι K := fun p b => Mg p.1.1 p.2 b
  have hinjR : Function.Injective (Matrix.toLin' R) := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro c hc
    rw [← hbot]
    simp only [kerS, Submodule.mem_iInf, LinearMap.mem_ker]
    intro g hg
    funext a
    have hc' : Matrix.mulVec R c = 0 := by rw [← Matrix.toLin'_apply]; exact LinearMap.mem_ker.1 hc
    have := congrFun hc' (⟨g, hg⟩, a)
    simpa [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, R] using this
  obtain ⟨Ψ, hΨ⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' R) (LinearMap.ker_eq_bot.2 hinjR)
  have hLR : LinearMap.toMatrix' Ψ * R = 1 := by
    have := congrArg LinearMap.toMatrix' hΨ
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id, LinearMap.toMatrix'_toLin'] at this
  have hLRC : (LinearMap.toMatrix' Ψ).map φ * R.map φ = 1 := by
    rw [← Matrix.map_mul, hLR, Matrix.map_one φ φ.map_zero φ.map_one]
  have hRd : Matrix.mulVec (R.map φ) d = 0 := by
    funext p
    have := congrFun (hdg p.1.1) p.2
    simp only [Matrix.mulVec, dotProduct] at this
    exact this
  apply hd
  calc d = Matrix.mulVec ((LinearMap.toMatrix' Ψ).map φ * R.map φ) d := by rw [hLRC, Matrix.one_mulVec]
    _ = 0 := by rw [← Matrix.mulVec_mulVec, hRd, Matrix.mulVec_zero]

theorem coeff_monic_poly_sum {R : Type} [Semiring R] (n k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ n) (c : ℕ → R) :
    (X ^ n + ∑ k' ∈ Finset.Icc 1 n, C (c k') * X ^ (n - k')).coeff (n - k) = c k := by
  rw [coeff_add, coeff_X_pow, if_neg (by omega), zero_add, finset_sum_coeff]
  rw [Finset.sum_eq_single k]
  · rw [coeff_C_mul_X_pow, if_pos rfl]
  · intro b hb hbk
    rw [coeff_C_mul_X_pow, if_neg]
    rw [Finset.mem_Icc] at hb
    omega
  · intro hk
    exact absurd (Finset.mem_Icc.2 ⟨hk1, hk2⟩) hk

theorem coeff_extract : ∀ {O : Type} [CommRing O] [IsLocalRing O] (ι : O →+* ℂ), Function.Injective ι → ∀ (n q : ℕ), IsUnit (q : O) → ∀ (p : O[X]) (lam : ℕ → ℂ) (t : ℕ → O), p.map ι = X ^ n + ∑ k ∈ Finset.Icc 1 n, C ((-1) ^ k * (q : ℂ) ^ (k * (k - 1) / 2) * lam k) * X ^ (n - k) → p.map (IsLocalRing.residue O) = (X ^ n + ∑ k ∈ Finset.Icc 1 n, C ((-1 : O) ^ k * (q : O) ^ (k * (k - 1) / 2) * t k) * X ^ (n - k)).map (IsLocalRing.residue O) → ∀ k, 1 ≤ k → k ≤ n → ∃ a : O, ι a = lam k ∧ IsLocalRing.residue O a = IsLocalRing.residue O (t k) := by
  intro O _ _ ι hι n q hq p lam t h1 h2 k hk1 hk2
  set u : O := (-1 : O) ^ k * (q : O) ^ (k * (k - 1) / 2) with hu_def
  have hu : IsUnit u := ((isUnit_one.neg).pow k).mul (hq.pow _)
  have e1 : ι (p.coeff (n - k)) = ι u * lam k := by
    have := congrArg (fun P : ℂ[X] => P.coeff (n - k)) h1
    simp only [coeff_map] at this
    rw [this, coeff_monic_poly_sum n k hk1 hk2 (fun k' => (-1) ^ k' * (q : ℂ) ^ (k' * (k' - 1) / 2) * lam k')]
    simp [u]
  have e2 : IsLocalRing.residue O (p.coeff (n - k)) = IsLocalRing.residue O (u * t k) := by
    have := congrArg (fun P : (IsLocalRing.ResidueField O)[X] => P.coeff (n - k)) h2
    simp only [coeff_map] at this
    rw [this, coeff_monic_poly_sum n k hk1 hk2 (fun k' => (-1 : O) ^ k' * (q : O) ^ (k' * (k' - 1) / 2) * t k')]
  refine ⟨↑hu.unit⁻¹ * p.coeff (n - k), ?_, ?_⟩
  · rw [map_mul, e1, ← mul_assoc, ← map_mul, hu.val_inv_mul, map_one, one_mul]
  · rw [map_mul, e2, ← map_mul, ← mul_assoc, hu.val_inv_mul, one_mul]

theorem normV_unit : ∀ (D : D7) (i : D.nd.Loc) (w : PlE D.host), w ∉ placesOver D.host.E (D.nd.l i) → IsUnit (((normV w : ℕ) : D.nd.O i)) := by
  intro D i w hw
  classical
  have hl : (D.nd.l i).Prime := (D.nd.lPrime i).out
  have hN : ¬ (D.nd.l i) ∣ normV w := by
    intro hdvd
    letI := Ideal.Quotient.field w.asIdeal
    haveI : Finite (𝓞 D.host.E ⧸ w.asIdeal) := w.asIdeal.finiteQuotientOfFreeOfNeBot w.ne_bot
    letI := Fintype.ofFinite (𝓞 D.host.E ⧸ w.asIdeal)
    obtain ⟨p, hchar⟩ := CharP.exists (𝓞 D.host.E ⧸ w.asIdeal)
    have hp : p.Prime := CharP.char_is_prime (𝓞 D.host.E ⧸ w.asIdeal) p
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨n, -, hn⟩ := FiniteField.card (𝓞 D.host.E ⧸ w.asIdeal) p
    have hcard : normV w = p ^ (n : ℕ) := by rw [normV, Nat.card_eq_fintype_card, hn]
    rw [hcard] at hdvd
    have hlp : D.nd.l i = p := (Nat.prime_dvd_prime_iff_eq hl hp).1 (hl.dvd_of_dvd_pow hdvd)
    apply hw
    show ((D.nd.l i : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, hlp]
    exact CharP.cast_eq_zero _ p
  have hu : IsUnit ((normV w : ℕ) : ℤ_[D.nd.l i]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact (Nat.Prime.coprime_iff_not_dvd hl).2 hN
  have := hu.map (algebraMap ℤ_[D.nd.l i] (D.nd.O i))
  rwa [map_natCast] at this

end GlobalTheory.PtLocalEig
