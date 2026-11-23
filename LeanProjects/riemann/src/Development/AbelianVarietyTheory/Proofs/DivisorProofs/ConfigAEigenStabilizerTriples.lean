import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAdelicSchwartzSpaceOfLevelCompactSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenSubgroupsSchroedingerFixStandardChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativelyCompactStabilizer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedAdelicLatticeClosure

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ConeLevel

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem rho_comm {R W κ : Type} [CommRing R] [Invertible (2 : R)] [AddCommGroup W] [Module R W] [Fintype κ]
    {B : W → W → R} (d : Darboux B κ) (ψ : AddChar R ℂ) (w w' : W) (h : B w w' = 0) (φ : (κ → R) → ℂ) :
    d.rho ψ w (d.rho ψ w' φ) = d.rho ψ w' (d.rho ψ w φ) := by
  have hf := d.form w w'
  rw [h] at hf
  funext x
  simp only [Darboux.rho, schr]
  rw [show x + (d.e w).1 + (d.e w').1 = x + (d.e w').1 + (d.e w).1 by abel]
  rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  congr 2
  simp only [add_dotProduct]
  linear_combination -hf

theorem symp_eq_zero {n d n₁ d₁ : ℕ} (σ : E →ₐ[F] E) (JX : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin d) (Fin d) E)
    (x₀ : Fin n → E) (ι : Matrix (Fin n) (Fin n₁) E) (hι : ∀ u, form σ JX (ι *ᵥ u) x₀ = 0)
    (ξ : AE F E) (z : Matrix (Fin n₁) (Fin d₁) (AE F E)) (C : Matrix (Fin d₁) (Fin d) (AE F E)) (t : AE F E)
    (y : Fin d → AE F E) :
    symp (cA σ) ξ (incM F JX) (incM F JW) (incM F ι * z * C) (t • Matrix.vecMulVec (incV F x₀) y) = 0 := by
  set a : Fin n → AE F E := incM F JX *ᵥ fun k => cA σ (incV F x₀ k) with ha
  set bb : Fin d → AE F E := incM F JW *ᵥ fun l => cA σ (y l) with hbb
  have ha' : a = fun i => inclR (F := F) (AF F) ((JX *ᵥ fun k => σ (x₀ k)) i) := by
    funext i
    rw [ha, RingHom.map_mulVec]
    rfl
  have key : a ᵥ* incM F ι = 0 := by
    funext j
    have h3 := hι (Pi.single j 1)
    rw [form, Matrix.mulVec_single_one] at h3
    have : a ᵥ* incM F ι = fun j => inclR (F := F) (AF F) (((JX *ᵥ fun k => σ (x₀ k)) ᵥ* ι) j) := by
      funext j
      rw [RingHom.map_vecMul, ha']
      rfl
    rw [this]
    simp only [Pi.zero_apply]
    rw [Matrix.vecMul, dotProduct_comm]
    exact (congrArg _ h3).trans (map_zero _)
  have hx : ∀ j, ∑ i, a i * (incM F ι * z * C) i j = 0 := by
    intro j
    have := congrFun (show a ᵥ* (incM F ι * z * C) = 0 by
      rw [← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, key, Matrix.zero_vecMul, Matrix.zero_vecMul]) j
    simpa [Matrix.vecMul, dotProduct] using this
  have hT : hTens (cA σ) (incM F JX) (incM F JW) (incM F ι * z * C) (t • Matrix.vecMulVec (incV F x₀) y) =
      ∑ j, (∑ i, a i * (incM F ι * z * C) i j) * (cA σ t * bb j) := by
    simp only [hTens]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [ha, hbb, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul, Matrix.smul_apply,
      Matrix.vecMulVec_apply, smul_eq_mul, map_mul]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [symp, hT]
  simp [hx]

end GlobalTheory.ConeLevel

namespace GlobalTheory.ConeLevel

def jf {F : Type} [Field F] [NumberField F] (κ : Type) : (κ → FiniteAdeleRing (𝓞 F) F) →+ (κ → AF F) :=
  AddMonoidHom.compLeft (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) κ

def pf {F : Type} [Field F] [NumberField F] (κ : Type) : (κ → AF F) →+ (κ → FiniteAdeleRing (𝓞 F) F) :=
  AddMonoidHom.compLeft (AddMonoidHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) κ

theorem jf_eq {F : Type} [Field F] [NumberField F] {κ : Type} (v : κ → FiniteAdeleRing (𝓞 F) F) :
    jf κ v = GlobalTheory.WeilCont.adeleJoin F 0 v :=
  funext fun i => (GlobalTheory.SchrFixNbhd.adeleJoin_zero_apply v i).symm

theorem continuous_jf {F : Type} [Field F] [NumberField F] {κ : Type} : Continuous (jf (F := F) κ) :=
  continuous_pi fun i => continuous_const.prodMk (continuous_apply i)

theorem continuous_pf {F : Type} [Field F] [NumberField F] {κ : Type} : Continuous (pf (F := F) κ) :=
  continuous_pi fun i => continuous_snd.comp (continuous_apply i)

theorem jf_pf {F : Type} [Field F] [NumberField F] {κ : Type} (u : κ → AF F) (hu : ∀ i, (u i).1 = 0) :
    jf κ (pf κ u) = u :=
  funext fun i => Prod.ext (hu i).symm rfl

def finOne (F : Type) [Field F] [NumberField F] : AF F := ((0 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F))

theorem finOne_mul_fst {F : Type} [Field F] [NumberField F] (a : AF F) : (finOne F * a).1 = 0 :=
  show (0 : InfiniteAdeleRing F) * a.1 = 0 from zero_mul _

theorem finOne_smul_jf {F : Type} [Field F] [NumberField F] {κ : Type} (v : κ → FiniteAdeleRing (𝓞 F) F) :
    finOne F • jf κ v = jf κ v :=
  funext fun i => Prod.ext (show (0 : InfiniteAdeleRing F) * 0 = 0 from zero_mul _)
    (show (1 : FiniteAdeleRing (𝓞 F) F) * v i = v i from one_mul _)

set_option maxHeartbeats 1000000 in
theorem level : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ (K : Subgroup (UA σ G.V.J)), IsStab B K →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ Ψ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')),
      ∃ U : AddSubgroup (Fin b × Fin (b + a') → AF F), IsOpen (U : Set (Fin b × Fin (b + a') → AF F)) ∧
        ∀ u ∈ U, (∀ i, (u i).1 = 0) → ∀ (k : K) (l : (AE F E)ˣ) (x : Fin b × Fin (b + a') → AF F),
          e (G.M.co.rho B.ψ (shiftA H H' l) (om (k.1, 1) Ψ)) (x + u) = e (G.M.co.rho B.ψ (shiftA H H' l) (om (k.1, 1) Ψ)) x := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' hC e he K hK X om om' om₁ om₁' hT hT₁ Ψ hΨ
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI hMT : ∀ m n : ℕ, IsModuleTopology (AF F) (Matrix (Fin m) (Fin n) (AE F E)) := fun m n =>
    inferInstanceAs (IsModuleTopology (AF F) (Fin m → Fin n → AE F E))
  have hstd : IsStd B.ψ := hT.base.std
  have hsplit := IsUWeilPair.isUSplitting hT.weil

  have hKc : IsCompact (K : Set (UA σ G.V.J)) := by
    have hKeq : K = GlobalTheory.StabHaar.stabK B G.V := by
      ext g
      exact hK g
    obtain ⟨C, hCc, hsub⟩ := GlobalTheory.StabBounded.exists_compact_superset_stabK F E σ B _ G.V _ _ hT.base hT.geo.hV
    rw [hKeq]
    exact hCc.of_isClosed_subset (GlobalTheory.StabHaar.isClosed_stabK B G.V
      (GlobalTheory.LatHatClosed.isClosed_latHat F E _ G.V hT.geo.hV.lat)) hsub

  obtain ⟨L₁, L₂, o₁, o₂, hfix⟩ := GlobalTheory.SchrFixNbhd.exists_fix F B.ψ hstd.1 _ Ψ hΨ

  let κ := Fin (b + 2) × Fin (b + 2 + a')
  let κ₁ := Fin b × Fin (b + a')
  let N₀ : Set ((κ → AF F) × (κ → AF F)) := {p | pf κ p.1 ∈ L₁ ∧ pf κ p.2 ∈ L₂}
  have hN₀ : IsOpen N₀ := (o₁.preimage (continuous_pf.comp continuous_fst)).inter
    (o₂.preimage (continuous_pf.comp continuous_snd))
  have h0N₀ : (0 : (κ → AF F) × (κ → AF F)) ∈ N₀ := ⟨by simp [map_zero], by simp [map_zero]⟩
  have hce : Continuous G.M.co.e := IsModuleTopology.continuous_of_linearMap G.M.co.e.toLinearMap
  have hce₁ : Continuous G₁.M.co.e.symm := IsModuleTopology.continuous_of_linearMap G₁.M.co.e.symm.toLinearMap
  have hm : Continuous fun g : UA σ G.V.J => mat g := Units.continuous_val.comp continuous_subtype_val
  have hcont : Continuous fun q : Matrix (Fin (b + 2)) (Fin (b + 2 + a')) (AE F E) × UA σ G.V.J =>
      G.M.co.e (mat q.2⁻¹ * q.1) :=
    hce.comp (((hm.comp continuous_inv).comp continuous_snd).matrix_mul continuous_fst)
  have tube : ∀ᶠ w in 𝓝 (0 : Matrix (Fin (b + 2)) (Fin (b + 2 + a')) (AE F E)),
      ∀ g ∈ (K : Set (UA σ G.V.J)), G.M.co.e (mat g⁻¹ * w) ∈ N₀ := by
    refine hKc.eventually_forall_of_forall_eventually fun g _ => ?_
    have h0 : G.M.co.e (mat g⁻¹ * (0 : Matrix (Fin (b + 2)) (Fin (b + 2 + a')) (AE F E))) ∈ N₀ := by rw [Matrix.mul_zero, map_zero]; exact h0N₀
    exact (hcont.tendsto ((0 : Matrix (Fin (b + 2)) (Fin (b + 2 + a')) (AE F E)), g)).eventually (hN₀.mem_nhds h0)

  let zz : (κ₁ → FiniteAdeleRing (𝓞 F) F) → Matrix (Fin b) (Fin (b + a')) (AE F E) :=
    fun v => G₁.M.co.e.symm (jf κ₁ v, 0)
  let ww : (κ₁ → FiniteAdeleRing (𝓞 F) F) → Matrix (Fin (b + 2)) (Fin (b + 2 + a')) (AE F E) :=
    fun v => incM F H.ι * zz v * (incM F H'.ι)ᵀ
  have hww : Continuous ww := (continuous_const.matrix_mul (hce₁.comp (continuous_jf.prodMk continuous_const))).matrix_mul
    continuous_const
  have hww0 : ww 0 = 0 := by
    simp only [ww, zz, map_zero, Prod.mk_zero_zero, Matrix.mul_zero, Matrix.zero_mul]
  have ev : ∀ᶠ v in 𝓝 (0 : κ₁ → FiniteAdeleRing (𝓞 F) F), ∀ g ∈ (K : Set (UA σ G.V.J)),
      G.M.co.e (mat g⁻¹ * ww v) ∈ N₀ := by
    have := hww.tendsto 0
    rw [hww0] at this
    exact this.eventually tube

  have hfinite : ∀ v (g : UA σ G.V.J), finOne F • G.M.co.e (mat g⁻¹ * ww v) = G.M.co.e (mat g⁻¹ * ww v) := by
    intro v g
    have h1 : finOne F • zz v = zz v := by
      simp only [zz]
      rw [← map_smul, Prod.smul_mk, smul_zero, finOne_smul_jf]
    have h2 : finOne F • ww v = ww v := by
      simp only [ww]
      rw [← Matrix.smul_mul, ← Matrix.mul_smul, h1]
    calc finOne F • G.M.co.e (mat g⁻¹ * ww v) = G.M.co.e (mat g⁻¹ * (finOne F • ww v)) := by
          rw [Matrix.mul_smul, map_smul]
      _ = _ := by rw [h2]
  have hΨfix : ∀ v, (∀ g ∈ (K : Set (UA σ G.V.J)), G.M.co.e (mat g⁻¹ * ww v) ∈ N₀) →
      ∀ g ∈ (K : Set (UA σ G.V.J)), G.M.co.rho B.ψ (mat g⁻¹ * ww v) Ψ = Ψ := by
    intro v hv g hg
    have hpf : finOne F • G.M.co.e (mat g⁻¹ * ww v) = G.M.co.e (mat g⁻¹ * ww v) := hfinite v g
    set p := G.M.co.e (mat g⁻¹ * ww v) with hp
    have e1 : p.1 = jf κ (pf κ p.1) := (jf_pf _ fun i => by rw [← hpf]; exact finOne_mul_fst _).symm
    have e2 : p.2 = jf κ (pf κ p.2) := (jf_pf _ fun i => by rw [← hpf]; exact finOne_mul_fst _).symm
    show schr B.ψ p Ψ = Ψ
    rw [show p = (GlobalTheory.WeilCont.adeleJoin F 0 (pf κ p.1), GlobalTheory.WeilCont.adeleJoin F 0 (pf κ p.2)) from
      Prod.ext (e1.trans (jf_eq _)) (e2.trans (jf_eq _))]
    exact hfix _ (hv g hg).1 _ (hv g hg).2
  let hh : K → (AE F E)ˣ → Fn F b (b + a') := fun k l => e (G.M.co.rho B.ψ (shiftA H H' l) (om (k.1, 1) Ψ))
  let T : AddSubgroup (κ₁ → AF F) := ⨅ k : K, ⨅ l : (AE F E)ˣ, GlobalTheory.SchrFixNbhd.fixTrans (hh k l)
  let S : AddSubgroup (κ₁ → FiniteAdeleRing (𝓞 F) F) := T.comap (jf κ₁)
  have key : ∀ v, (∀ g ∈ (K : Set (UA σ G.V.J)), G.M.co.e (mat g⁻¹ * ww v) ∈ N₀) → v ∈ S := by
    intro v hv
    simp only [S, T, AddSubgroup.mem_comap, AddSubgroup.mem_iInf]
    intro k l x
    have hfixk := hΨfix v hv k.1 k.2
    have hΦ₁ : om (k.1, 1) Ψ ∈ schA F κ := hsplit.pres _ _ hΨ
    have hΦ₂ := GlobalTheory.HeisSchA.rho_mem_schA G.M B.ψ hstd (shiftA H H' l) _ hΦ₁
    have htr : ∀ f : Fn F b (b + a'), f (x + jf κ₁ v) = G₁.M.co.rho B.ψ (zz v) f x := by
      intro f
      simp only [Darboux.rho, schr, zz, LinearEquiv.apply_symm_apply, dotProduct_zero, mul_zero, add_zero,
        AddChar.map_zero_eq_one, one_mul]
    show hh k l (x + jf κ₁ v) = hh k l x
    simp only [hh]
    rw [htr (e (G.M.co.rho B.ψ (shiftA H H' l) (om (k.1, 1) Ψ))), ← he.Heisenberg₂ _ _ hΦ₂]
    rw [rho_comm G.M.co B.ψ (incM F H.ι * zz v * (incM F H'.ι)ᵀ) (shiftA H H' l)
      (symp_eq_zero σ G.V.J G.W.J H.x H.ι (fun u => (hC.hH.orth u).1) (-1) (zz v) _ l.1 _)]
    have himpl := hsplit.impl (k.1, 1) (mat k.1⁻¹ * ww v) Ψ hΨ
    have hact : actAB (cA σ) ((k.1, 1) : UA σ G.V.J × UA σ G.W.J) (mat k.1⁻¹ * ww v) = ww v := by
      show mat k.1 * (mat k.1⁻¹ * ww v) * (mat (1 : UA σ G.W.J))ᵀ = ww v
      rw [GlobalTheory.StabHaar.mat_one, Matrix.transpose_one, Matrix.mul_one, ← Matrix.mul_assoc,
        GlobalTheory.StabHaar.mat_mul_inv, Matrix.one_mul]
    rw [hact, hfixk] at himpl
    rw [← himpl]
  have hS : IsOpen (S : Set (κ₁ → FiniteAdeleRing (𝓞 F) F)) :=
    AddSubgroup.isOpen_of_mem_nhds S (Filter.mem_of_superset ev key)
  refine ⟨S.comap (pf κ₁), hS.preimage continuous_pf, fun u hu hu0 k l x => ?_⟩
  have hu' : jf κ₁ (pf κ₁ u) ∈ T := hu
  rw [jf_pf u hu0] at hu'
  exact (AddSubgroup.mem_iInf.1 (AddSubgroup.mem_iInf.1 hu' k) l) x

end GlobalTheory.ConeLevel
