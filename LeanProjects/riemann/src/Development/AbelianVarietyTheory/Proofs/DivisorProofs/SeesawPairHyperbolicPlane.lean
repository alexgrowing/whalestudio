import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HfMulVecMulVec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermUnipotentIntegral
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactAdeleRingModNumberFieldStatement

open scoped TensorProduct NNReal Matrix

noncomputable section
namespace GlobalTheory.HermEichler

variable {R : Type} [CommRing R] {c : R →+* R} {n m : ℕ} {J : Matrix (Fin n) (Fin n) R}

private theorem continuous_eich [TopologicalSpace R] [IsTopologicalRing R] (hcc : Continuous c) (x : Fin n → R)
    (ι : Matrix (Fin n) (Fin m) R) {T : Type} [TopologicalSpace T] {a : T → R} {v : T → Fin m → R}
    (ha : Continuous a) (hv : Continuous v) : Continuous fun t => eich c J x ι (a t) (v t) := by
  refine continuous_matrix fun i j => ?_
  simp only [eich, Matrix.add_apply, Matrix.sub_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  fun_prop

private theorem continuous_hf [TopologicalSpace R] [IsTopologicalRing R] (hcc : Continuous c)
    (ι : Matrix (Fin n) (Fin m) R) : Continuous fun v : Fin m → R => hf c J (ι *ᵥ v) (ι *ᵥ v) := by
  simp only [hf, Matrix.mulVec, dotProduct]
  fun_prop

private theorem eq_eich (hc : ∀ r, c (c r) = r) (hJ : ∀ i j, c (J j i) = J i j) {x y : Fin n → R}
    {ι : Matrix (Fin n) (Fin m) R} (hxx : hf c J x x = 0) (hyy : hf c J y y = 0) (hxy : hf c J x y = 1)
    (hιx : ∀ z, hf c J (ι *ᵥ z) x = 0) (hιy : ∀ z, hf c J (ι *ᵥ z) y = 0)
    (hdec : ∀ t : Fin n → R, ∃ (s r : R) (z : Fin m → R), t = s • x + ι *ᵥ z + r • y)
    {g : Matrix (Fin n) (Fin n) R} (hg : gᵀ * J * g.map c = J) (hgx : g *ᵥ x = x)
    (hgι : ∀ z, ∃ a : R, g *ᵥ (ι *ᵥ z) = ι *ᵥ z + a • x) :
    ∃ a v, a + c a + hf c J (ι *ᵥ v) (ι *ᵥ v) = 0 ∧ g = eich c J x ι a v := by
  have hyx : hf c J y x = 1 := by rw [hf_herm c J hc hJ, hxy, map_one]
  have hxι : ∀ z, hf c J x (ι *ᵥ z) = 0 := fun z => by rw [hf_herm c J hc hJ, hιx, map_zero]
  have hyι : ∀ z, hf c J y (ι *ᵥ z) = 0 := fun z => by rw [hf_herm c J hc hJ, hιy, map_zero]
  have hu : ∀ s t, hf c J (g *ᵥ s) (g *ᵥ t) = hf c J s t := fun s t => by rw [hf_mulVec_mulVec, hg]
  obtain ⟨a, r, v, hy⟩ := hdec (g *ᵥ y)
  have hr : r = 1 := by
    have := hu y x
    rw [hgx, hy] at this
    simpa [hf_add_left, hf_smul_left, hxx, hιx, hyx] using this
  subst hr
  rw [one_smul] at hy
  refine ⟨a, v, ?_, ?_⟩
  · have := hu y y
    rw [hy] at this
    simp only [hf_add_left, hf_smul_left, hf_add_right, hf_smul_right, hxx, hιx, hyx, hxι, hyι, hxy, hyy, hιy] at this
    linear_combination this
  · refine Matrix.ext_of_mulVec_single fun k => ?_
    obtain ⟨s, r, z, ht⟩ := hdec (Pi.single k 1)
    obtain ⟨b, hb⟩ := hgι z
    have hb' : b = -hf c J (ι *ᵥ z) (ι *ᵥ v) := by
      have := hu (ι *ᵥ z) y
      rw [hy, hb] at this
      simp only [hf_add_left, hf_smul_left, hf_add_right, hf_smul_right, hxx, hιx, hyx, hxι, hyι, hxy, hyy, hιy] at this
      linear_combination this
    rw [ht]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul]
    rw [hgx, hb, hy, eich_mulVec_x_eq_x hc hJ hxx hιx, eich_mulVec_ι hιx, eich_mulVec_y hyx hyι, hb']
    congr 2
    abel

private theorem hf_map {K : Type} [CommRing K] (f : K →+* R) (c₀ : K →+* K) (hf' : ∀ r, f (c₀ r) = c (f r))
    (J₀ : Matrix (Fin n) (Fin n) K) (s t : Fin n → K) :
    hf c (J₀.map f) (fun i => f (s i)) (fun i => f (t i)) = f (hf c₀ J₀ s t) := by
  simp [hf, dotProduct, Matrix.mulVec, hf']

private theorem mulVec_eq_sum (ι : Matrix (Fin n) (Fin m) R) (z : Fin m → R) :
    ι *ᵥ z = ∑ j, z j • fun i => ι i j := by
  ext i; simp [Matrix.mulVec, dotProduct, mul_comm]

private theorem hf_map_ι {K : Type} [CommRing K] (f : K →+* R) (c₀ : K →+* K) (hf' : ∀ r, f (c₀ r) = c (f r))
    (J₀ : Matrix (Fin n) (Fin n) K) (ι : Matrix (Fin n) (Fin m) K) (t : Fin n → K) (h : ∀ z, hf c₀ J₀ (ι *ᵥ z) t = 0)
    (z : Fin m → R) : hf c (J₀.map f) (ι.map f *ᵥ z) (fun i => f (t i)) = 0 := by
  have h1 : ∀ j, hf c (J₀.map f) (fun i => ι.map f i j) (fun i => f (t i)) = 0 := fun j => by
    have := hf_map f c₀ hf' J₀ (ι *ᵥ Pi.single j 1) t
    rw [h, map_zero, Matrix.mulVec_single_one] at this
    exact this
  rw [mulVec_eq_sum, hf, sum_dotProduct]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [smul_dotProduct]
  exact smul_eq_zero_of_right _ (h1 j)

private theorem dec_map {K : Type} [CommRing K] (f : K →+* R) {x y : Fin n → K} {ι : Matrix (Fin n) (Fin m) K}
    (hdec : ∀ t : Fin n → K, ∃ (s r : K) (z : Fin m → K), t = s • x + ι *ᵥ z + r • y) (t : Fin n → R) :
    ∃ (s r : R) (z : Fin m → R), t = s • (fun i => f (x i)) + ι.map f *ᵥ z + r • fun i => f (y i) := by
  choose s r z h using fun k => hdec (Pi.single k 1)
  refine ⟨∑ k, t k * f (s k), ∑ k, t k * f (r k), fun j => ∑ k, t k * f (z k j), ?_⟩
  ext i
  have h1 : t i = ∑ k, t k * f ((Pi.single k 1 : Fin n → K) i) := by
    rw [Finset.sum_eq_single i] <;> simp +contextual [Pi.single_apply, eq_comm]
  rw [h1]
  simp only [h, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, map_add, map_mul, map_sum,
    Matrix.map_apply, Finset.mul_sum, Finset.sum_mul, mul_add, Finset.sum_add_distrib]
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin m)))]
  congr 1
  · congr 1
    · exact Finset.sum_congr rfl fun _ _ => by ring
    · exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  · exact Finset.sum_congr rfl fun _ _ => by ring

private def eichGL (hc : ∀ r, c (c r) = r) (hJ : ∀ i j, c (J j i) = J i j) {x : Fin n → R}
    {ι : Matrix (Fin n) (Fin m) R} (hxx : hf c J x x = 0) (hιx : ∀ z, hf c J (ι *ᵥ z) x = 0) (a : R) (v : Fin m → R) :
    GL (Fin n) R :=
  ⟨eich c J x ι a v, eich c J x ι (-a - hf c J (ι *ᵥ v) (ι *ᵥ v)) (-v), (eich_mul_inv hc hJ hxx hιx a v).1,
    (eich_mul_inv hc hJ hxx hιx a v).2⟩

private theorem cocompact [TopologicalSpace R] [IsTopologicalRing R] (hcc : Continuous c) (hc : ∀ r, c (c r) = r)
    {K : Type} [Field K] [CharZero K] (f : K →+* R) (c₀ : K →+* K) (hc₀ : ∀ r, c₀ (c₀ r) = r)
    (hf' : ∀ r, f (c₀ r) = c (f r)) {J₀ : Matrix (Fin n) (Fin n) K} (hJ₀ : ∀ i j, c₀ (J₀ j i) = J₀ i j)
    {x y : Fin n → K} {ι : Matrix (Fin n) (Fin m) K} (hn : m + 2 = n) (hxx : hf c₀ J₀ x x = 0) (hyy : hf c₀ J₀ y y = 0)
    (hxy : hf c₀ J₀ x y = 1) (hιx : ∀ z, hf c₀ J₀ (ι *ᵥ z) x = 0) (hιy : ∀ z, hf c₀ J₀ (ι *ᵥ z) y = 0)
    (hinj : Function.Injective ι.mulVec) {C : Set R} (hC : IsCompact C) (hCs : ∀ r, ∃ k, r - f k ∈ C)
    (P : GL (Fin n) R → Prop) (hP : ∀ g, P g ↔ g.1ᵀ * J₀.map f * g.1.map c = J₀.map f ∧
      g.1 *ᵥ (fun i => f (x i)) = (fun i => f (x i)) ∧
      ∀ z, ∃ a : R, g.1 *ᵥ (ι.map f *ᵥ z) = ι.map f *ᵥ z + a • fun i => f (x i)) :
    ∃ S : Set (GL (Fin n) R), IsCompact S ∧ (∀ g ∈ S, P g) ∧ ∀ g, P g → ∃ γ : GL (Fin n) K,
      P (Matrix.GeneralLinearGroup.map f γ) ∧ Matrix.GeneralLinearGroup.map f γ * g ∈ S := by
  have hyx : hf c₀ J₀ y x = 1 := by rw [hf_herm c₀ J₀ hc₀ hJ₀, hxy, map_one]
  have hdec := dec_map f (decomp hn hxy hyx hxx hyy hιx hιy hinj)
  have hJ : ∀ i j, c (J₀.map f j i) = J₀.map f i j := fun i j => by
    rw [Matrix.map_apply, ← hf', hJ₀, Matrix.map_apply]
  have Hxx := hf_map f c₀ hf' J₀ x x
  have Hyy := hf_map f c₀ hf' J₀ y y
  have Hxy := hf_map f c₀ hf' J₀ x y
  rw [hxx, map_zero] at Hxx
  rw [hyy, map_zero] at Hyy
  rw [hxy, map_one] at Hxy
  have Hιx := hf_map_ι f c₀ hf' J₀ ι x hιx
  have Hιy := hf_map_ι f c₀ hf' J₀ ι y hιy
  have hPe : ∀ (g : GL (Fin n) R) a v, a + c a + hf c (J₀.map f) (ι.map f *ᵥ v) (ι.map f *ᵥ v) = 0 →
      g.1 = eich c (J₀.map f) (fun i => f (x i)) (ι.map f) a v → P g := fun g a v h1 h2 => by
    rw [hP, h2]
    exact ⟨eich_unitary hc hJ Hxx Hιx h1, eich_mulVec_x_eq_x hc hJ Hxx Hιx a v, fun z => ⟨_, eich_mulVec_ι Hιx a v z⟩⟩
  set e : R := f (1 / 2) with he
  have he2 : 2 * e = 1 := by rw [he, ← map_ofNat f 2, ← map_mul]; simp
  have hce : c e = e := by rw [he, ← hf']; simp [map_ofNat]
  let N : (Fin m → R) → R := fun v => hf c (J₀.map f) (ι.map f *ᵥ v) (ι.map f *ᵥ v)
  have hN : ∀ v, c (N v) = N v := fun v => (hf_herm c _ hc hJ _ _).symm
  have hNc : Continuous N := continuous_hf hcc _
  let A : R × (Fin m → R) → R := fun p => e * (p.1 - c p.1 - N p.2)
  have hA : Continuous A := by fun_prop
  let Φ : R × (Fin m → R) → GL (Fin n) R := fun p => eichGL hc hJ Hxx Hιx (A p) p.2
  have hΦ : Continuous Φ := Units.continuous_iff.2
    ⟨continuous_eich hcc _ _ hA continuous_snd,
      continuous_eich hcc _ _ (hA.neg.sub (hNc.comp continuous_snd)) continuous_snd.neg⟩
  refine ⟨Φ '' (C ×ˢ Set.pi Set.univ fun _ => C), (hC.prod (isCompact_univ_pi fun _ => hC)).image hΦ, ?_, fun g hg => ?_⟩
  · rintro _ ⟨p, -, rfl⟩
    refine hPe _ (A p) p.2 ?_ rfl
    change A p + c (A p) + N p.2 = 0
    simp only [A, map_mul, map_sub, hce, hc, hN]
    linear_combination (-N p.2) * he2
  · obtain ⟨h1, h2, h3⟩ := (hP g).1 hg
    obtain ⟨a, v, ha, hga⟩ := eq_eich hc hJ Hxx Hyy Hxy Hιx Hιy hdec h1 h2 h3
    choose w hw using fun j => hCs (v j)
    set N₀ := hf c₀ J₀ (ι *ᵥ (-w)) (ι *ᵥ (-w)) with hN₀
    have hcN₀ : c₀ N₀ = N₀ := (hf_herm c₀ _ hc₀ hJ₀ _ _).symm
    have hfN₀ : f N₀ = N fun j => f ((-w) j) := by
      rw [hN₀, ← hf_map f c₀ hf']
      have : (fun i => f ((ι *ᵥ (-w)) i)) = ι.map f *ᵥ fun j => f ((-w) j) := funext fun i => RingHom.map_mulVec _ _ _ _
      rw [this]
    set B := hf c (J₀.map f) (ι.map f *ᵥ v) (ι.map f *ᵥ fun j => f ((-w) j)) with hB
    obtain ⟨k, hk⟩ := hCs (-(e * f N₀) + a - B)
    set a₀ : K := 1 / 2 * (c₀ k - k - N₀) with ha₀
    have hfa₀ : f a₀ = e * (c (f k) - f k - f N₀) := by rw [ha₀, map_mul, map_sub, map_sub, hf']
    have hcf : c (f N₀) = f N₀ := by rw [← hf', hcN₀]
    have hγ : (Matrix.GeneralLinearGroup.map f (eichGL hc₀ hJ₀ hxx hιx a₀ (-w))).1 =
        eich c (J₀.map f) (fun i => f (x i)) (ι.map f) (f a₀) fun j => f ((-w) j) := eich_map f c hf' x ι a₀ (-w)
    have hcon : f a₀ + c (f a₀) + N (fun j => f ((-w) j)) = 0 := by
      rw [← hfN₀, hfa₀]
      simp only [map_mul, map_sub, hce, hc, hcf]
      linear_combination (-f N₀) * he2
    refine ⟨eichGL hc₀ hJ₀ hxx hιx a₀ (-w), hPe _ _ _ hcon hγ,
      (-(e * f N₀) + a - B - f k, fun j => v j - f (w j)), ⟨hk, fun j _ => hw j⟩, Units.ext ?_⟩
    have hv : (fun j => v j - f (w j)) = (fun j => f ((-w) j)) + v := by
      funext j; simp [sub_eq_neg_add]
    have h5 := con_mul hc hJ hcon ha
    rw [Units.val_mul, hγ, hga, eich_mul hc hJ Hxx Hιx, ← hv]
    rw [← hv, ← hB] at h5
    change eich _ _ _ _ (A _) _ = _
    congr 1
    change _ + _ + N _ = 0 at h5
    rw [← hB]
    simp only [A]
    generalize N (fun j => v j - f (w j)) = Z at h5 ⊢
    simp only [hfa₀, map_mul, map_sub, map_add, map_neg, hce, hc, hcf] at h5 ⊢
    linear_combination (-e) * h5 + (e * (c (f k) - f k - f N₀) + a - B) * he2 + (e * (f k - c (f k))) * he2

end GlobalTheory.HermEichler
end

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

private theorem tens_cocompact (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    ∃ K : Set (AF F ⊗[F] E), IsCompact K ∧ ∀ z, ∃ x : E, z - inclR (F := F) (AF F) x ∈ K := by
  obtain ⟨K, hK, h⟩ := GlobalTheory.T.exists_compact_adeleRing_mod_numberField F
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  let b := Module.finBasis F E
  let e := (Algebra.TensorProduct.basis (AF F) b).equivFun
  have he : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  refine ⟨e.symm '' Set.pi Set.univ fun _ => K, (isCompact_univ_pi fun _ => hK).image he, fun z => ?_⟩
  choose x hx using fun i => h (e z i)
  refine ⟨∑ i, x i • b i, fun i => e z i - algebraMap F _ (x i), fun i _ => hx i, ?_⟩
  have : (fun i => e z i - algebraMap F (AF F) (x i)) = e z - fun i => algebraMap F (AF F) (x i) := rfl
  rw [this, map_sub, LinearEquiv.symm_apply_apply, map_sum]
  congr 1
  rw [Module.Basis.equivFun_symm_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [algebraMap_smul, Algebra.TensorProduct.basis_apply, ← TensorProduct.tmul_smul]
  rfl

theorem _root_.GlobalTheory.T.seesaw_pair_hyperbolic_plane : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' →
    ∀ (d₂ : ℕ) (H : Plane E n d₂), (d₂ + 2 = n ∧ form σ X.J H.x H.x = 0 ∧ form σ X.J H.y H.y = 0 ∧ form σ X.J H.x H.y = 1 ∧
        (∀ u, form σ X.J (H.ι *ᵥ u) H.x = 0 ∧ form σ X.J (H.ι *ᵥ u) H.y = 0) ∧ Function.Injective H.ι.mulVec) →
    ∃ K : Set (UA σ X.J), IsCompact K ∧ K ⊆ unip σ X H ∧ ∀ u ∈ unip σ X H, ∃ γ ∈ ratU σ X.J, γ ∈ unip σ X H ∧ γ * u ∈ K := by
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₂ H ⟨hn, hxx, hyy, hxy, hι, hinj⟩
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hcA : Continuous (cA (F := F) σ) := IsModuleTopology.continuous_of_linearMap (cA (F := F) σ).toLinearMap
  have hσ : ∀ x, σ (σ x) = x := fun x => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hP.base.cm.2.2.2, hP.base.cm.2.2.2, star_star]
  have hc : ∀ z : AE F E, cA σ (cA σ z) = z := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => exact congrArg (a ⊗ₜ[F] ·) (hσ x)
    | add x y hx hy => simp only [map_add, hx, hy]
  obtain ⟨C, hC, hCs⟩ := tens_cocompact F E
  obtain ⟨S, hS, h1, h2⟩ := GlobalTheory.HermEichler.cocompact (c := (cA (F := F) σ : AE F E →+* AE F E)) hcA hc
    (inclR (F := F) (AF F)) (σ : E →+* E) hσ (fun _ => rfl) (J₀ := X.J) hP.herm.herm (x := H.x) (y := H.y) (ι := H.ι)
    hn hxx hyy hxy (fun z => (hι z).1) (fun z => (hι z).2) hinj hC hCs _ (fun _ => Iff.rfl)
  rw [GlobalTheory.UnipCT.unip_eq]
  refine ⟨Subtype.val ⁻¹' S, Topology.IsInducing.subtypeVal.isCompact_preimage' hS fun g hg => ⟨⟨g, (h1 g hg).1⟩, rfl⟩,
    fun u hu => (h1 u.1 hu).2, fun u hu => ?_⟩
  obtain ⟨γ, hγ, hγu⟩ := h2 u.1 ⟨u.2, hu⟩
  exact ⟨⟨_, hγ.1⟩, ⟨γ, rfl⟩, hγ.2, hγu⟩
