import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameOnOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.StepLaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocalApprox

open GlobalTheory.IdemSupport Filter Topology

section Indicator

variable (F : Type) [Field F] [NumberField F]

def intFam (x : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F :=
  RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite x

theorem continuous_intFam : Continuous (intFam F) := by
  unfold intFam
  exact RestrictedProduct.isEmbedding_structureMap.continuous

open Classical in

def indA (s : Finset (HeightOneSpectrum (𝓞 F))) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F :=
  intFam F fun v => if v ∈ s then 1 else 0

theorem evalV_indA_of_mem {s : Finset (HeightOneSpectrum (𝓞 F))} {v : HeightOneSpectrum (𝓞 F)} (h : v ∈ s) :
    evalV F v (indA F s) = 1 := by
  classical
  show ((if v ∈ s then (1 : v.adicCompletionIntegers F) else 0 : v.adicCompletionIntegers F) : v.adicCompletion F) = 1
  rw [if_pos h]
  rfl

theorem evalV_indA_of_notMem {s : Finset (HeightOneSpectrum (𝓞 F))} {v : HeightOneSpectrum (𝓞 F)} (h : v ∉ s) :
    evalV F v (indA F s) = 0 := by
  classical
  show ((if v ∈ s then (1 : v.adicCompletionIntegers F) else 0 : v.adicCompletionIntegers F) : v.adicCompletion F) = 0
  rw [if_neg h]
  rfl

theorem af_ext {a b : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F} (h : ∀ v, evalV F v a = evalV F v b) : a = b := Subtype.ext (funext fun v => h v)

theorem indA_mem (s : Finset (HeightOneSpectrum (𝓞 F))) : indA F s ∈ Formalism.UG.intAd F := by
  classical
  refine fun v => ?_
  exact (if v ∈ s then (1 : v.adicCompletionIntegers F) else 0).2

theorem indA_mul_self (s : Finset (HeightOneSpectrum (𝓞 F))) : indA F s * indA F s = indA F s := by
  apply af_ext F
  intro v
  rw [map_mul]
  by_cases h : v ∈ s
  · rw [evalV_indA_of_mem F h, mul_one]
  · rw [evalV_indA_of_notMem F h, mul_zero]

theorem indA_empty : indA F ∅ = 0 := by
  apply af_ext F
  intro v
  rw [evalV_indA_of_notMem F (by simp), map_zero]

theorem indA_cons {s : Finset (HeightOneSpectrum (𝓞 F))} {v : HeightOneSpectrum (𝓞 F)} (h : v ∉ s) :
    indA F (Finset.cons v s h) = indA F {v} + indA F s ∧ indA F {v} * indA F s = 0 := by
  constructor
  · apply af_ext F
    intro w
    rw [map_add]
    by_cases hw : w = v
    · subst hw
      rw [evalV_indA_of_mem F (by simp), evalV_indA_of_mem F (by simp), evalV_indA_of_notMem F h, add_zero]
    · by_cases hs : w ∈ s
      · rw [evalV_indA_of_mem F (by simp [hs]), evalV_indA_of_notMem F (by simpa using hw),
          evalV_indA_of_mem F hs, zero_add]
      · rw [evalV_indA_of_notMem F (by simp [hw, hs]), evalV_indA_of_notMem F (by simpa using hw),
          evalV_indA_of_notMem F hs, add_zero]
  · apply af_ext F
    intro w
    rw [map_mul, map_zero]
    by_cases hw : w = v
    · subst hw
      rw [evalV_indA_of_notMem F h, mul_zero]
    · rw [evalV_indA_of_notMem F (by simpa using hw), zero_mul]

theorem tendsto_indA : Tendsto (indA F) atTop (𝓝 1) := by
  classical
  have h1 : intFam F (fun _ => 1) = 1 := af_ext F fun v => by
    rw [map_one]
    rfl
  have hp : Tendsto (fun s : Finset (HeightOneSpectrum (𝓞 F)) =>
      fun v : HeightOneSpectrum (𝓞 F) => (if v ∈ s then 1 else 0 : v.adicCompletionIntegers F))
      atTop (𝓝 fun _ => 1) := by
    rw [tendsto_pi_nhds]
    intro v
    apply tendsto_const_nhds.congr'
    filter_upwards [Filter.eventually_ge_atTop {v}] with s hs
    rw [if_pos (hs (Finset.mem_singleton_self v))]
  have h2 := ((continuous_intFam F).tendsto _).comp hp
  rw [h1] at h2
  convert h2 using 1
  funext s
  unfold indA
  simp only [Function.comp_apply]

end Indicator

section Generic

variable {A B : Type} [CommRing A] [CommRing B] {n : Type} [Fintype n] [DecidableEq n]

omit [Fintype n] in
theorem mix_map (ψ : A →+* B) (f : A) (a : Matrix n n A) :
    (f • a + (1 - f) • (1 : Matrix n n A)).map ψ = ψ f • a.map ψ + (1 - ψ f) • (1 : Matrix n n B) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs <;> simp

theorem mix_add {f f' : A} (h : f * f' = 0) (a : Matrix n n A) :
    (f • a + (1 - f) • (1 : Matrix n n A)) * (f' • a + (1 - f') • (1 : Matrix n n A)) =
      (f + f') • a + (1 - (f + f')) • (1 : Matrix n n A) := by
  have h1 : f * (1 - f') = f := by rw [mul_sub, h, mul_one, sub_zero]
  have h2 : (1 - f) * f' = f' := by rw [sub_mul, one_mul, h, sub_zero]
  have h3 : (1 - f) * (1 - f') = 1 - (f + f') := by linear_combination h
  simp only [add_mul, mul_add, smul_mul_smul_comm, mul_one, one_mul, h, h1, h2, h3, zero_smul, zero_add]
  rw [add_smul]
  abel

theorem mix_conj (f : A) (β : GL n A) (y : Matrix n n A) :
    β.val * (f • y + (1 - f) • (1 : Matrix n n A)) * (β⁻¹).val =
      f • (β.val * y * (β⁻¹).val) + (1 - f) • (1 : Matrix n n A) := by
  have hb : β.val * (β⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  simp only [mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hb]

omit [Fintype n] in
theorem tendsto_mix [TopologicalSpace A] [IsTopologicalRing A] {ι : Type} {l : Filter ι} {f : ι → A} {e : A}
    (hf : Tendsto f l (𝓝 e)) (a : Matrix n n A) (ha : ∀ i j, e * (a - 1) i j = (a - 1) i j) :
    Tendsto (fun s => f s • a + (1 - f s) • (1 : Matrix n n A)) l (𝓝 a) := by
  have hlim : e • a + (1 - e) • (1 : Matrix n n A) = a := by
    ext i j
    have h := ha i j
    simp only [Matrix.sub_apply] at h
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    linear_combination h
  have h := (hf.smul_const a).add ((tendsto_const_nhds (x := (1 : A))).sub hf |>.smul_const (1 : Matrix n n A))
  rwa [hlim] at h

theorem piece_conj (S : Subring B) (ψ : A →+* B) {f : A} (hf : f * f = f) (hm : ψ f ∈ S) (β : GL n B) (g : GL n A)
    (y : GL n S) (hy : β * Formalism.UG.bc S.subtype y * β⁻¹ = Formalism.UG.bc ψ g) :
    ∃ y' : GL n S, β * Formalism.UG.bc S.subtype y' * β⁻¹ = Formalism.UG.bc ψ (piece hf g) := by
  have hf' : (⟨ψ f, hm⟩ : S) * ⟨ψ f, hm⟩ = ⟨ψ f, hm⟩ := by
    apply Subtype.ext
    show ψ f * ψ f = ψ f
    rw [← map_mul, hf]
  refine ⟨piece hf' y, ?_⟩
  have hy' : β.val * (y : Matrix n n S).map S.subtype * (β⁻¹).val = (g : Matrix n n A).map ψ :=
    congrArg Units.val hy
  have key : ((piece hf' y : GL n S) : Matrix n n S).map S.subtype =
      ψ f • (y : Matrix n n S).map S.subtype + (1 - ψ f) • (1 : Matrix n n B) := mix_map S.subtype _ _
  have key2 : ((piece hf g : GL n A) : Matrix n n A).map ψ =
      ψ f • (g : Matrix n n A).map ψ + (1 - ψ f) • (1 : Matrix n n B) := mix_map ψ _ _
  apply Units.ext
  show β.val * ((piece hf' y : GL n S) : Matrix n n S).map S.subtype * (β⁻¹).val =
    ((piece hf g : GL n A) : Matrix n n A).map ψ
  rw [key, key2, mix_conj, hy']

end Generic

variable {D : D7}

def idemE (D : D7) (s : Finset (HeightOneSpectrum (𝓞 D.host.F))) : AE D :=
  algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (indA D.host.F s))

theorem pairA_mul (F : Type) [Field F] [NumberField F] (a b : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) :
    pairA F 0 a * pairA F 0 b = pairA F 0 (a * b) := by
  show ((0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F) * 0, a * b) = ((0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F), a * b)
  rw [mul_zero]

theorem idemE_mul_self (s : Finset (HeightOneSpectrum (𝓞 D.host.F))) : idemE D s * idemE D s = idemE D s := by
  unfold idemE
  rw [← map_mul, pairA_mul, indA_mul_self]

theorem idemE_empty : idemE D ∅ = 0 := by
  unfold idemE
  rw [indA_empty]
  exact map_zero _
private theorem pairA_zero_add' (F : Type) [Field F] [NumberField F] (a b : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) :
    pairA F 0 (a + b) = pairA F 0 a + pairA F 0 b := by
  show ((0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F), a + b) = ((0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F) + 0, a + b)
  rw [add_zero]

theorem idemE_cons {s : Finset (HeightOneSpectrum (𝓞 D.host.F))} {v : HeightOneSpectrum (𝓞 D.host.F)} (h : v ∉ s) :
    idemE D (Finset.cons v s h) = idemE D {v} + idemE D s ∧ idemE D {v} * idemE D s = 0 := by
  obtain ⟨h1, h2⟩ := indA_cons D.host.F h
  constructor
  · unfold idemE
    rw [h1, pairA_zero_add', map_add]
  · unfold idemE
    rw [← map_mul, pairA_mul, h2]
    exact map_zero _

theorem isPlaceIdem_single (v : HeightOneSpectrum (𝓞 D.host.F)) :
    IsPlaceIdem D v (pairA D.host.F 0 (indA D.host.F {v})) := ⟨indA D.host.F {v}, rfl, evalV_indA_of_mem D.host.F (by simp),
    fun v' hv' => evalV_indA_of_notMem D.host.F (by simpa using hv')⟩

theorem placeIdem_mul_idemE {s : Finset (HeightOneSpectrum (𝓞 D.host.F))} {v : HeightOneSpectrum (𝓞 D.host.F)}
    (h : v ∈ s) {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) :
    algebraMap (AF D.host.F) (AE D) ε * idemE D s = algebraMap (AF D.host.F) (AE D) ε := by
  obtain ⟨α, rfl, -, h0⟩ := hε
  unfold idemE
  rw [← map_mul, pairA_mul]
  congr 2
  apply af_ext D.host.F
  intro w
  rw [map_mul]
  by_cases hw : w = v
  · subst hw
    rw [evalV_indA_of_mem D.host.F h, mul_one]
  · rw [h0 w hw, zero_mul]

theorem one_fin_mul {z : AE D} (hz : infPart D z = 0) :
    algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 1) * z = z := by
  have hsum : pairA D.host.F 0 1 = 1 - pairA D.host.F 1 0 := by
    show ((0 : Ainf D.host.F), (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)) =
      ((1 : Ainf D.host.F) - 1, (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) - 0)
    rw [sub_self, sub_zero]
  have key : ∀ w : AE D, algebraMap (AF D.host.F) (AE D) (pairA D.host.F 1 0) * w =
      TensorProduct.map (LinearMap.inl D.host.F (Ainf D.host.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)) LinearMap.id
        (infPart D w) := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp only [mul_zero, map_zero]; try rfl
    | tmul a x =>
      simp only [infPart, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
        AlgHom.id_apply, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul, TensorProduct.map_tmul, LinearMap.id_apply]
      congr 1
      show (1 * a.1, 0 * a.2) = (a.1, 0)
      rw [one_mul, zero_mul]
    | add a b ha hb => rw [mul_add, ha, hb, map_add, map_add]; try rfl
  rw [hsum, map_sub, map_one, sub_mul, one_mul, key, hz, map_zero]
  exact sub_zero z

theorem tendsto_idemE : Tendsto (idemE D) atTop (𝓝 (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 1))) := by
  have hc1 : Continuous (fun a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F => pairA D.host.F 0 a) :=
    Continuous.prodMk continuous_const continuous_id
  have hc2 : Continuous (algebraMap (AF D.host.F) (AE D)) := by
    have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
    exact (continuous_id.smul continuous_const).congr fun a => (Algebra.algebraMap_eq_smul_one a).symm
  exact ((hc2.comp hc1).tendsto _).comp (tendsto_indA D.host.F)

def cutAt (V : HSp D) (g : GA D V) (s : Finset (HeightOneSpectrum (𝓞 D.host.F))) : GA D V :=
  ⟨piece (idemE_mul_self s) g.1, piece_mem _ _ (idemE_mul_self s) (cA_algebraMap _) g.2⟩

theorem mt_cutAt (V : HSp D) (g : GA D V) (s : Finset (HeightOneSpectrum (𝓞 D.host.F))) :
    Formalism.L2.Theta.mt V (cutAt V g s) = idemE D s • Formalism.L2.Theta.mt V g + (1 - idemE D s) • (1 : Matrix _ _ (AE D)) := rfl

theorem cutAt_supp (V : HSp D) (g : GA D V) (s : Finset (HeightOneSpectrum (𝓞 D.host.F))) (i j : Fin V.rank) :
    idemE D s * (Formalism.L2.Theta.mt V (cutAt V g s) - 1) i j = (Formalism.L2.Theta.mt V (cutAt V g s) - 1) i j := by
  rw [mt_cutAt]
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  have hf := idemE_mul_self (D := D) s
  linear_combination ((Formalism.L2.Theta.mt V g) i j - (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) * hf
private theorem infComponent_idemE_eq_zero (s : Finset (HeightOneSpectrum (𝓞 D.host.F))) :
    infPart D (idemE D s) = 0 := by
  unfold idemE
  show (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E))
    ((pairA D.host.F 0 (indA D.host.F s)) ⊗ₜ[D.host.F] (1 : D.host.E)) = 0
  rw [Algebra.TensorProduct.map_tmul]
  show (0 : Ainf D.host.F) ⊗ₜ[D.host.F] _ = 0
  exact TensorProduct.zero_tmul _ _

theorem cutAt_mem_GfC (V : HSp D) (g : GA D V) (s : Finset (HeightOneSpectrum (𝓞 D.host.F))) :
    cutAt V g s ∈ GfC V := by
  show infHom V (cutAt V g s) = 1
  apply Units.ext
  show (Formalism.L2.Theta.mt V (cutAt V g s)).map (infPart D) = 1
  rw [mt_cutAt, mix_map, infComponent_idemE_eq_zero, zero_smul, zero_add, sub_zero, one_smul]

theorem cutAt_mem_St (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) {g : GA D V} (hg : finE V g ∈ St β)
    (s : Finset (HeightOneSpectrum (𝓞 D.host.F))) : finE V (cutAt V g s) ∈ St β := by
  obtain ⟨y, hy⟩ := hg
  have hm : ((Formalism.IndefR.Lev.swapAE D).comp (finPart D)) (idemE D s) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    have h1 : ((Formalism.IndefR.Lev.swapAE D).comp (finPart D)) (idemE D s) =
        algebraMap (𝓞 D.host.E) D.host.E 1 ⊗ₜ[D.host.F] indA D.host.F s := by
      rw [map_one]
      unfold idemE
      show (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E)
        ((Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E))
          ((pairA D.host.F 0 (indA D.host.F s)) ⊗ₜ[D.host.F] (1 : D.host.E))) = _
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.comm_tmul]
      rfl
    rw [h1]
    exact Formalism.UG.P.levelaf_tmul_mem (E := D.host.E) 1 (indA_mem D.host.F s)
  have hy' : β * Formalism.UG.bc (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype y * β⁻¹ =
      Formalism.UG.bc ((Formalism.IndefR.Lev.swapAE D).comp (finPart D)) g.1 := hy
  obtain ⟨y', hy''⟩ := piece_conj (Formalism.L2.Herm.intAf D.host.F D.host.E)
    ((Formalism.IndefR.Lev.swapAE D).comp (finPart D)) (idemE_mul_self s) hm β g.1 y hy'
  exact ⟨y', hy''⟩

theorem cutAt_empty (V : HSp D) (g : GA D V) : cutAt V g ∅ = 1 := by
  apply GlobalTheory.IdemSupport.mt_inj
  rw [mt_cutAt, GlobalTheory.IdemSupport.mt_one, idemE_empty, zero_smul, zero_add, sub_zero, one_smul]

theorem cutAt_cons (V : HSp D) (g : GA D V) {s : Finset (HeightOneSpectrum (𝓞 D.host.F))}
    {v : HeightOneSpectrum (𝓞 D.host.F)} (h : v ∉ s) :
    cutAt V g (Finset.cons v s h) = cutAt V g {v} * cutAt V g s := by
  apply GlobalTheory.IdemSupport.mt_inj
  obtain ⟨h1, h2⟩ := idemE_cons (D := D) h
  rw [GlobalTheory.IdemSupport.mt_mul, mt_cutAt, mt_cutAt, mt_cutAt, h1, mix_add h2]

theorem one_fin_supp (V : HSp D) {g : GA D V} (hg : g ∈ GfC V) (i j : Fin V.rank) :
    algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 1) * (Formalism.L2.Theta.mt V g - 1) i j =
      (Formalism.L2.Theta.mt V g - 1) i j := by
  apply one_fin_mul
  have hg' : (Formalism.L2.Theta.mt V g).map (infPart D) = 1 := congrArg Units.val (show infHom V g = 1 from hg)
  have h3 := congrFun (congrFun hg' i) j
  simp only [Matrix.map_apply] at h3
  rw [Matrix.sub_apply, map_sub, h3, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem tendsto_cutAt (V : HSp D) {g : GA D V} (hg : g ∈ GfC V) : Tendsto (cutAt V g) atTop (𝓝 g) := by
  have key : ∀ h : GA D V, h ∈ GfC V →
      Tendsto (fun s => Formalism.L2.Theta.mt V (cutAt V h s)) atTop (𝓝 (Formalism.L2.Theta.mt V h)) := by
    intro h hh
    have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
    have := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
    simp only [mt_cutAt]
    exact tendsto_mix tendsto_idemE _ (one_fin_supp V hh)
  have hinv : ∀ s, (cutAt V g s)⁻¹ = cutAt V g⁻¹ s := by
    intro s
    rw [inv_eq_iff_mul_eq_one]
    apply GlobalTheory.IdemSupport.mt_inj
    rw [GlobalTheory.IdemSupport.mt_mul, mt_cutAt, mt_cutAt, GlobalTheory.IdemSupport.mix_mul (idemE_mul_self s),
      ← GlobalTheory.IdemSupport.mt_mul, mul_inv_cancel, GlobalTheory.IdemSupport.mt_one, Matrix.mul_one,
      GlobalTheory.IdemSupport.mix_self]
  have hind : Topology.IsInducing (fun h : GA D V =>
      (Formalism.L2.Theta.mt V h, MulOpposite.op (Formalism.L2.Theta.mt V h⁻¹))) :=
    Units.isEmbedding_embedProduct.isInducing.comp Topology.IsInducing.subtypeVal
  rw [hind.tendsto_nhds_iff]
  refine Tendsto.prodMk_nhds (key g hg) ?_
  refine (MulOpposite.continuous_op.tendsto _).comp ?_
  simp only [hinv]
  exact key g⁻¹ (inv_mem hg)

theorem exists_local_approx : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)), ∀ g ∈ GfC V, finE V g ∈ St β → ∃ γ : Finset (HeightOneSpectrum (𝓞 D.host.F)) → GA D V, Filter.Tendsto γ Filter.atTop (nhds g) ∧ ∀ s, γ s ∈ Subgroup.closure {k : GA D V | k ∈ GfC V ∧ finE V k ∈ St β ∧ ∃ v ε, IsPlaceIdem D v ε ∧ SuppPl ε V k} ∧ ∀ v ∈ s, ∀ ε, IsPlaceIdem D v ε → ∀ i j, algebraMap (AF D.host.F) (AE D) ε * Formalism.L2.Theta.mt V (γ s) i j = algebraMap (AF D.host.F) (AE D) ε * Formalism.L2.Theta.mt V g i j := by
  intro D V β g hg hst
  refine ⟨cutAt V g, tendsto_cutAt V hg, fun s => ⟨?_, fun v hv ε hε i j => ?_⟩⟩
  · induction s using Finset.cons_induction with
    | empty =>
      rw [cutAt_empty]
      exact Subgroup.one_mem _
    | cons v s h ih =>
      rw [cutAt_cons V g h]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨cutAt_mem_GfC V g {v}, cutAt_mem_St V β hst {v}, v,
        pairA D.host.F 0 (indA D.host.F {v}), isPlaceIdem_single v, cutAt_supp V g {v}⟩) ih
  · rw [mt_cutAt]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    have hx := placeIdem_mul_idemE (D := D) hv hε
    linear_combination ((Formalism.L2.Theta.mt V g) i j - (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) * hx

end GlobalTheory.LocalApprox

end
