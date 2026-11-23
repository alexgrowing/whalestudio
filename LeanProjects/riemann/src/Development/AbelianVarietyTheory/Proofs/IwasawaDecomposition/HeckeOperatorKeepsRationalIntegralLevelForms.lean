import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DatVtEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtLvlFormMemCutSp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TranslatedStdLatticeLatticeComparisonRational
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdFrameLevelSubgroupBoundedOpenHyperspecialStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemRationalGLOfUnitaryGroupGramUnitGram
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LeExpNegOneOfLtOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteLevelFormsIffStdGroupTypeSpaceStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicFormFunctionValuesMemCoefficientLatticeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDoubleCosetOperatorsStandardFacts
import Formalism.LocalToGlobal.Columns.CoefModAt

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MtInHecke

section

open Formalism.L2.Col Formalism.HermitianLatticesTheory Module

section Comm

variable {K : Type} [Field K] [NumberField K]

theorem localized_eq_of_commensurable {W : Type} [AddCommGroup W] [Module (𝓞 K) W] (w : HeightOneSpectrum (𝓞 K))
    {M M' : Submodule (𝓞 K) W} {s : 𝓞 K} (hs : s ∉ w.asIdeal) (h1 : ∀ x ∈ M, s • x ∈ M') (h2 : ∀ x ∈ M', s • x ∈ M) :
    Formalism.HermitianLatticesTheory.localization₂ w.asIdeal M = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal M' := by
  apply le_antisymm
  · rintro x ⟨t, ht, hx⟩
    exact ⟨s * t, lc_mul_notMem w hs ht, by rw [mul_smul]; exact h1 _ hx⟩
  · rintro x ⟨t, ht, hx⟩
    exact ⟨s * t, lc_mul_notMem w hs ht, by rw [mul_smul]; exact h2 _ hx⟩

theorem localized_comap {V W : Type} [AddCommGroup V] [Module (𝓞 K) V] [AddCommGroup W] [Module (𝓞 K) W]
    (w : HeightOneSpectrum (𝓞 K)) (f : V →ₗ[𝓞 K] W) (N : Submodule (𝓞 K) W) :
    Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (N.comap f) = (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal N).comap f := by
  ext x
  simp only [lc_mem_locP, Submodule.mem_comap, map_smul]

theorem lat_dualFr_comm {n : ℕ} {M M' : Submodule (𝓞 K) (Fin n → K)} {s : 𝓞 K} (h : ∀ y ∈ M, s • y ∈ M') :
    ∀ x ∈ dualFr M', s • x ∈ dualFr M := by
  intro x hx y hy
  show (s • x) ⬝ᵥ y ∈ (1 : Submodule (𝓞 K) K)
  rw [smul_dotProduct, ← dotProduct_smul]
  exact hx _ (h y hy)

variable {E : Type} [Field E] [NumberField E] {ι : Type} [Fintype ι] {n : ℕ} (emb : ι → E →+* K)

theorem lat_tauLat_comm (τ : ι) {L L' : Submodule (𝓞 E) (Fin n → E)} {q : ℕ} (h : ∀ x ∈ L, (q : 𝓞 E) • x ∈ L') :
    ∀ y ∈ tauLat emb τ L, (q : 𝓞 K) • y ∈ tauLat emb τ L' := by
  intro y hy
  have hle : tauLat emb τ L ≤ (tauLat emb τ L').comap (LinearMap.lsmul (𝓞 K) (Fin n → K) (q : 𝓞 K)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    show (q : 𝓞 K) • (fun a => emb τ (x a)) ∈ tauLat emb τ L'
    refine Submodule.subset_span ⟨(q : 𝓞 E) • x, h x hx, ?_⟩
    funext a
    simp [Algebra.smul_def]
  exact hle hy

theorem localized_nabla_eq_of_commensurable (lam : ι → DomWeight n) (w : HeightOneSpectrum (𝓞 K)) {L L' : Submodule (𝓞 E) (Fin n → E)}
    (hL : Submodule.IsLattice E L) (hL' : Submodule.IsLattice E L') {q : ℕ} (h1 : ∀ x ∈ L, (q : 𝓞 E) • x ∈ L')
    (h2 : ∀ x ∈ L', (q : 𝓞 E) • x ∈ L) (hq : (q : 𝓞 K) ∉ w.asIdeal) :
    Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabAtr emb lam L) = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabAtr emb lam L') := by
  have hM : ∀ τ, Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (dualFr (tauLat emb τ L)) = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (dualFr (tauLat emb τ L')) :=
    fun τ => localized_eq_of_commensurable w hq (lat_dualFr_comm (lat_tauLat_comm emb τ h2))
      (lat_dualFr_comm (lat_tauLat_comm emb τ h1))
  have hlat := fun τ => dualFr_tauLat_isLattice emb τ L hL
  have hlat' := fun τ => dualFr_tauLat_isLattice emb τ L' hL'
  choose B hB using fun τ => latticeBasisExists_holds K n (dualFr (tauLat emb τ L)) (hlat τ) w
  have hB' : ∀ τ, IsBasisAt w (dualFr (tauLat emb τ L')) (B τ) := fun τ => by
    unfold IsBasisAt
    rw [← hM τ]
    exact hB τ
  unfold nabAtr nabK
  rw [localized_comap, localized_comap]
  congr 1
  unfold nabP
  rw [nb_loc (nb_stab_nab lam) (nb_comm_nab lam) _ hlat w B hB, nb_loc (nb_stab_nab lam) (nb_comm_nab lam) _ hlat' w B hB']

end Comm

end

theorem heckeD_mem {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W]
    (Λ : Formalism.AUTREP.GAf L n → AddSubmonoid W) (J : Subgroup (Formalism.AUTREP.GAf L n)) (T : Set (Formalism.AUTREP.GAf L n))
    (hΛ : ∀ g, ∀ x ∈ T, Λ (g * x) ≤ Λ g) (f : Formalism.AUTREP.GAf L n → W) (hf : ∀ g, f g ∈ Λ g) (g : Formalism.AUTREP.GAf L n) :
    NG.heckeD J T f g ∈ Λ g := by
  classical
  unfold NG.heckeD
  apply finsum_induction (fun w => w ∈ Λ g)
  · exact (Λ g).zero_mem
  · intro a b ha hb; exact (Λ g).add_mem ha hb
  · intro c
    split_ifs with hc
    · exact hΛ g _ hc.choose_spec.1 (hf _)
    · exact (Λ g).zero_mem

theorem tN_val {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
    {K U : Type} [Field K] [AddCommGroup U] [Module K U] {σ : K →+* ℂ} (c0 : U →ₛₗ[σ] W)
    (Λ : Formalism.AUTREP.GAf L n → AddSubmonoid U) (J : Subgroup (Formalism.AUTREP.GAf L n)) (s : ReciprocityTheory.Aut.SplitPlace L)
    (ϖ : s.v.adicCompletion (maximalRealSubfield L)) (k : ℕ)
    (hΛ : ∀ g, ∀ x ∈ Formalism.AUTREP.tSet L n s ϖ k, Λ (g * x) ≤ Λ g) (f : Formalism.AUTREP.GAf L n → W)
    (hf : ∀ g, ∃ v ∈ Λ g, f g = c0 v) (g : Formalism.AUTREP.GAf L n) :
    ∃ v ∈ Λ g, NG.tN J s ϖ k f g = c0 (((s.q : K) ^ (k * (n - 1)))⁻¹ • v) := by
  obtain ⟨v, hv, e⟩ := heckeD_mem (fun g => (Λ g).map c0.toAddMonoidHom) J _
    (fun g x hx => AddSubmonoid.monotone_map (hΛ g x hx)) f
    (fun g => by obtain ⟨v, hv, e⟩ := hf g; exact ⟨v, hv, e.symm⟩) g
  refine ⟨v, hv, ?_⟩
  show ((s.q : ℂ) ^ (k * (n - 1)))⁻¹ • NG.heckeD J (Formalism.AUTREP.tSet L n s ϖ k) f g = _
  rw [← e, map_smulₛₗ, map_inv₀, map_pow, map_natCast]
  rfl

section Lvl

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K) {G₀ : Type} [Group G₀] [Fintype G₀]
    (r : Representation K G₀ S.Forms) (P : Subgroup G₀) (ψ : P →* Kˣ)

def lvlLin : (Fin (S.lvlDim r P ψ) → K) →ₗ[K] S.Forms :=
  (S.basis.equivFun.symm : (Fin S.dim → K) →ₗ[K] S.Forms) ∘ₗ (S.lvlE r P ψ).mulVecLin

theorem lvlLin_apply (x : Fin (S.lvlDim r P ψ) → K) : lvlLin S r P ψ x = lvlForm S r P ψ x := rfl

theorem ext_mem_span {G Γ W : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] {ι : Γ →* G}
    {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ} (pres : Bridge.ClassPres ι S σ ρ J χ)
    (x : Fin (S.lvlDim r P ψ) → K) :
    pres.ext (lvlForm S r P ψ x).1 ∈
      Submodule.span ℂ (Set.range fun a => pres.ext (lvlForm S r P ψ (Pi.single a 1)).1) := by
  have e : pres.ext (lvlForm S r P ψ x).1 = ∑ a, σ (x a) • pres.ext (lvlForm S r P ψ (Pi.single a 1)).1 := by
    show pres.extL (lvlLin S r P ψ x) = ∑ a, σ (x a) • pres.extL (lvlLin S r P ψ (Pi.single a 1))
    conv_lhs => rw [pi_eq_sum_univ' x]
    simp only [map_sum, map_smul, map_smulₛₗ]
  rw [e]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

theorem clear_den (w : HeightOneSpectrum (𝓞 K)) (x : Fin (S.lvlDim r P ψ) → K)
    (h : ∀ c, ∃ t : 𝓞 K, t ∉ w.asIdeal ∧ t • (lvlForm S r P ψ x).1 c ∈ S.Nab c) :
    ∃ d : 𝓞 K, d ∉ w.asIdeal ∧ ∀ c, (lvlForm S r P ψ (d • x)).1 c ∈ S.Nab c := by
  classical
  choose t ht hm using h
  refine ⟨∏ c, t c, ?_, fun c => ?_⟩
  · exact (w.asIdeal.primeCompl (hp := w.isPrime)).prod_mem (fun c _ => ht c)
  · have e : (lvlForm S r P ψ ((∏ c, t c) • x)).1 c = (∏ c, t c) • (lvlForm S r P ψ x).1 c := by
      rw [← algebraMap_smul K (∏ c, t c) x, ← lvlLin_apply, map_smul, ← algebraMap_smul K (∏ c, t c)]
      rfl
    rw [e, ← Finset.prod_erase_mul _ _ (Finset.mem_univ c), mul_smul]
    exact Submodule.smul_mem _ _ (hm c)

end Lvl

theorem inv_smul_locP {K U : Type} [Field K] [NumberField K] [AddCommGroup U] [Module K U] [Module (𝓞 K) U]
    [IsScalarTower (𝓞 K) K U] (w : HeightOneSpectrum (𝓞 K)) (M : Submodule (𝓞 K) U) {q : ℕ} (N : ℕ)
    (hq : (q : 𝓞 K) ∉ w.asIdeal) {v : U} (hv : v ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal M) :
    ∃ t : 𝓞 K, t ∉ w.asIdeal ∧ t • (((q : K) ^ N)⁻¹ • v) ∈ M := by
  obtain ⟨t, ht, hv⟩ := hv
  have hq0 : (q : K) ≠ 0 := by
    intro h
    have : q = 0 := by exact_mod_cast h
    apply hq
    rw [this, Nat.cast_zero]
    exact w.asIdeal.zero_mem
  refine ⟨t * (q : 𝓞 K) ^ N, fun h => ?_, ?_⟩
  · rcases w.isPrime.mem_or_mem h with h | h
    · exact ht h
    · exact hq (w.isPrime.mem_of_pow_mem _ h)
  · rw [mul_smul, ← algebraMap_smul K ((q : 𝓞 K) ^ N), map_pow, map_natCast, smul_smul ((q : K) ^ N),
      mul_inv_cancel₀ (pow_ne_zero _ hq0), one_smul]
    exact hv

variable {D : D7}

theorem lev_int (V : HSp D) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) (k : Bridge.Gf V) (hk : k ∈ (levEnv V 1 L).J) (a b) :
    swapAE D (k.1.val a b) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  have h : Formalism.UG.bc (swapAE D) k.1 ∈ lev D.sp.cm V.gram 1 (flag1L L) := hk
  obtain ⟨y, hy⟩ := parLev_St h.1
  have e : intGL D.host.F D.host.E V.rank y = Formalism.UG.bc (swapAE D) k.1 := by
    rw [← hy]; simp [frGL]
  have e2 : ((y.val a b : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) = swapAE D (k.1.val a b) :=
    congrArg (fun g : GL (Fin V.rank) (EAf D) => g.val a b) e
  rw [← e2]
  exact (y.val a b).2

theorem hLat_lev (V : HSp D) (hV : Seed.FrmC.StdLat V) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) :
    ∀ k ∈ (levEnv V 1 L).J, ∀ h, Bridge.hLat V (h * k) = Bridge.hLat V h := by
  have key : ∀ k ∈ (levEnv V 1 L).J, ∀ h, Bridge.hLat V h ≤ Bridge.hLat V (h * k) := by
    intro k hk h y hy
    have := (GlobalTheory.HLatStd.hLat_props D V hV).2.1 h k 1 (fun a b => by
      rw [Nat.cast_one, one_mul]; exact lev_int V L _ (inv_mem hk) a b) y hy
    rwa [Nat.cast_one, one_smul] at this
  intro k hk h
  refine le_antisymm ?_ (key k hk h)
  have := key k⁻¹ (inv_mem hk) (h * k)
  rwa [mul_inv_cancel_right] at this

theorem swap_toGf {V : HSp D} (P : principalLevelFrame.RowPsi V V.rank) (hU : UnitFr P) (x) (a b) :
    swapAE D ((toGf P x).1.val a b) = (km D V.rank x).val a b := by
  rw [← hU x]; rfl

theorem localization_nabAtr_eq' {V : HSp D} (hV : Seed.FrmC.StdLat V)
    (lam : D.what₂.Tau → DomWeight V.rank) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) {p : ℕ} (hp : (p : 𝓞 D.what₂.LL) ∉ w.asIdeal)
    (h y : Bridge.Gf V)
    (hy : ∀ a b, (p : EAf D) * swapAE D (y.1.val a b) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (hy' : ∀ a b, (p : EAf D) * swapAE D ((y⁻¹ : Bridge.Gf V).1.val a b) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabAtr (labLL D) lam (Bridge.hLat V (h * y))) =
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabAtr (labLL D) lam (Bridge.hLat V h)) := by
  obtain ⟨h1, h2, -⟩ := GlobalTheory.HLatStd.hLat_props D V hV
  have a1 := h2 (h * y) y⁻¹ p (fun a b => by rw [inv_inv]; exact hy a b)
  rw [mul_inv_cancel_right] at a1
  exact localized_nabla_eq_of_commensurable _ lam w (h1 _) (h1 _) a1 (h2 h y p hy') hp

theorem line₅ {V : HSp D} (hV : Seed.FrmC.StdLat V) (P : principalLevelFrame.RowPsi V V.rank) (hU : UnitFr P)
    (lam : D.what₂.Tau → DomWeight V.rank) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) {p : ℕ} (hp : (p : 𝓞 D.what₂.LL) ∉ w.asIdeal)
    (g x : Formalism.AUTREP.GAf D.host.E V.rank)
    (hx : ∀ a b, (p : EAf D) * (km D V.rank x).val a b ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧
      (p : EAf D) * (km D V.rank x⁻¹).val a b ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabAtr (labLL D) lam (Bridge.hLat V (toGf P (g * x)))) =
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabAtr (labLL D) lam (Bridge.hLat V (toGf P g))) := by
  have e1 : toGf P (g * x) = toGf P g * toGf P x := (toGf P).map_mul g x
  have e2 : (toGf P x)⁻¹ = toGf P x⁻¹ := ((toGf P).map_inv x).symm
  rw [e1]
  refine localization_nabAtr_eq' hV lam w hp _ _ (fun a b => ?_) (fun a b => ?_)
  · rw [swap_toGf P hU]; exact (hx a b).1
  · rw [e2, swap_toGf P hU]; exact (hx a b).2

set_option maxHeartbeats 1600000 in

theorem tN_core {V : HSp D} {c : CoefA V} (P : principalLevelFrame.RowPsi V V.rank) (hg : V.gram = 1) (hV : Seed.FrmC.StdLat V) (hU : UnitFr P)
    {J : Subgroup (Bridge.Gf V)} {χ : J →* ℂˣ} {Qg : Subgroup (Bridge.Gf V)} {ch : Qg →* ℂˣ}
    {G₀ : Type} [Group G₀] [Fintype G₀] (S : CSD D.what₂.LL) (act : Representation D.what₂.LL G₀ S.Forms)
    (pres : Bridge.ClassPres (Bridge.ratF V) S D.what₂.embLL c.coef.ρ J χ) (tie : Bridge.ActTie (Bridge.ratF V) pres Qg ch act)
    (P₀ : Subgroup G₀) (ψ : P₀ →* D.what₂.LLˣ) (lam : D.what₂.Tau → DomWeight V.rank)
    (c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] c.W) (pair del) (hmap : Bridge.CoefMapTie V c.coef c0 (rhoVr (labLL D) lam))
    (hcoef : Bridge.CoefTie V c.coef pres lam c0 pair (nabAtr (labLL D) lam) del)
    (hlev : ∀ k ∈ J, ∀ h, Bridge.hLat V (h * k) = Bridge.hLat V h)
    (hint : ∀ k : J, ∃ z : 𝓞 D.what₂.LL, D.what₂.embLL (z : D.what₂.LL) = (χ k : ℂ))
    (Js : Subgroup (Formalism.AUTREP.GAf D.host.E V.rank)) (TS : Set (Formalism.AUTREP.GAf D.host.E V.rank → c.W))
    (htype : ∀ F : Bridge.Gf V → c.W, F ∈ cutSp (Bridge.ratF V) c.coef.ρ J χ Qg ch tie.red P₀
      ((Units.map D.what₂.embLL.toMonoidHom).comp ψ) ↔ (fun g => F (toGf P g)) ∈ TS)
    (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)) (k : ℕ)
    (hϖ : Formalism.AUTREP.IsUnif D.host.E s.v ϖ) (hTS : ∀ f ∈ TS, NG.tN Js s ϖ k f ∈ TS) (x) :
    ∃ x', (fun g => pres.ext (lvlForm S act P₀ ψ x').1 (toGf P g)) =
        NG.tN Js s ϖ k (fun g => pres.ext (lvlForm S act P₀ ψ x).1 (toGf P g)) ∧
      ∀ 𝔴 : HeightOneSpectrum (𝓞 D.what₂.LL), (∀ p : ℕ, p.Prime → s.Above p → (p : 𝓞 D.what₂.LL) ∉ 𝔴.asIdeal) →
        x ∈ S.lvlNab act P₀ ψ → ∃ d : 𝓞 D.what₂.LL, d ∉ 𝔴.asIdeal ∧ d • x' ∈ S.lvlNab act P₀ ψ := by
  obtain ⟨-, hspan, hrat, hnab, hy, hinj⟩ := GlobalTheory.MtIn.lvlForm_adelic_basis _ _ _ _ _ S _ _ _ _ pres _ _ G₀ act tie P₀ ψ
  have hbij := (GlobalTheory.MtInRat.toGf_bij_ratIso D V P hg hU).1
  have hvals := GlobalTheory.T.adelicFormFunction_values_mem_coefficientLattice D V hV c S _ _ pres lam c0 pair del hmap hcoef hlev hint (lvlForm S act P₀ ψ x)
  have hF0 := ext_mem_span S act P₀ ψ pres x
  rw [hspan] at hF0
  have hT := hTS _ ((htype _).1 hF0)
  obtain ⟨eV, -, hce, -, hN, -⟩ := hcoef
  obtain ⟨u, hu, hu'⟩ : ∃ u : Bridge.Gf V → Formalism.AUTREP.GAf D.host.E V.rank,
      (∀ g, u (toGf P g) = g) ∧ ∀ h, toGf P (u h) = h :=
    ⟨Function.surjInv hbij.2, Function.leftInverse_surjInv hbij, Function.surjInv_eq hbij.2⟩
  have hval := fun Λ h1 h2 => tN_val c0 Λ Js s ϖ k h1 (fun g => pres.ext (lvlForm S act P₀ ψ x).1 (toGf P g)) h2
  have hv1 : ∀ g, ∃ v ∈ (⊤ : AddSubmonoid (VV D.what₂.LL lam)), pres.ext (lvlForm S act P₀ ψ x).1 (toGf P g) = c0 v :=
    fun g => (Set.mem_range.1 (hvals.1 (toGf P g))).imp fun v hv => ⟨trivial, hv.symm⟩
  obtain ⟨T, hTd⟩ : ∃ T : Formalism.AUTREP.GAf D.host.E V.rank → c.W,
      T = NG.tN (W := c.W) Js s ϖ k (fun g => pres.ext (lvlForm S act P₀ ψ x).1 (toGf P g)) := ⟨_, rfl⟩
  replace hT : T ∈ TS := by rw [hTd]; exact hT
  replace hval : ∀ Λ : Formalism.AUTREP.GAf D.host.E V.rank → AddSubmonoid (VV D.what₂.LL lam),
      (∀ g, ∀ y ∈ Formalism.AUTREP.tSet D.host.E V.rank s ϖ k, Λ (g * y) ≤ Λ g) →
      (∀ g, ∃ v ∈ Λ g, pres.ext (lvlForm S act P₀ ψ x).1 (toGf P g) = c0 v) →
      ∀ g, ∃ v ∈ Λ g, T g = c0 (((s.q : D.what₂.LL) ^ (k * (V.rank - 1)))⁻¹ • v) := by
    rw [hTd]; exact hval
  have hTu : (fun g => T (u (toGf P g))) = T := funext fun g => congrArg T (hu g)
  have hT' : (fun g => T (u (toGf P g))) ∈ TS := by rw [hTu]; exact hT
  have hcut := (htype (fun h => T (u h))).2 hT'
  obtain ⟨x', hx'⟩ := hrat _ hcut (fun a => by
    obtain ⟨v, -, hv⟩ := hval (fun _ => ⊤) (fun _ _ _ => le_rfl) hv1 (u (pres.y a))
    exact ⟨eV.symm _, (hce _).trans ((congrArg c0 (eV.apply_symm_apply _)).trans hv.symm)⟩)
  refine ⟨x', (funext fun g => (congrFun hx' (toGf P g)).symm).trans (hTu.trans hTd), fun w hw hx => ?_⟩
  obtain ⟨p, hp, hab, ⟨m, hq⟩, hts⟩ := GlobalTheory.TSetDenom.tSet_denominator D V.rank s ϖ k hϖ
  have hpw := hw p hp hab
  have hqw : ((s.q : ℕ) : 𝓞 D.what₂.LL) ∉ w.asIdeal := fun h => hpw (w.isPrime.mem_of_pow_mem m (by
    rwa [hq, Nat.cast_pow] at h))
  have hint' := hvals.2 ((hnab x).1 hx)
  obtain ⟨d, hd, hdm⟩ := clear_den S act P₀ ψ w x' (fun a => by
    obtain ⟨v, hvm, hv⟩ := hval
      (fun g => (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabAtr (labLL D) lam (Bridge.hLat V (toGf P g)))).toAddSubmonoid)
      (fun g y hy => le_of_eq (congrArg Submodule.toAddSubmonoid (line₅ hV P hU lam w hpw g y (hts y hy))))
      (fun g => by
        obtain ⟨v, hv, e⟩ := hint' (toGf P g)
        exact ⟨v, ⟨1, (w.asIdeal.primeCompl (hp := w.isPrime)).one_mem, by rwa [one_smul]⟩, e⟩) (u (pres.y a))
    rw [hu'] at hvm
    obtain ⟨t, ht, htm⟩ := inv_smul_locP w _ (k * (V.rank - 1)) hqw hvm
    refine ⟨t, ht, ?_⟩
    have e1 : (lvlForm S act P₀ ψ x').1 a = eV.symm (((s.q : D.what₂.LL) ^ (k * (V.rank - 1)))⁻¹ • v) := by
      apply hinj
      exact (hy _ a).symm.trans ((congrFun hx' _).symm.trans
        (hv.trans ((hce _).trans (congrArg c0 (eV.apply_symm_apply _))).symm))
    rw [← hN a] at htm
    obtain ⟨z, hz, hze⟩ := htm
    have : t • (lvlForm S act P₀ ψ x').1 a = z := by
      apply eV.injective
      rw [e1, ← algebraMap_smul D.what₂.LL t, map_smul, LinearEquiv.apply_symm_apply, algebraMap_smul]
      exact hze.symm
    rw [this]; exact hz)
  exact ⟨d, hd, (hnab _).2 hdm⟩

set_option maxHeartbeats 1600000 in

theorem tN_lvlForm : ∀ (D : D7) (V : HSp D) (hr : D.R.r ≤ V.rank) (Pg Q : Finset (Pl D.host.E)) (chi xi : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (c : CoefA V) (P : principalLevelFrame.RowPsi V V.rank) (e : ReciprocityTheory.Aut.GQ D.host.E V.rank ≃* Formalism.L2.Theta.GQ V), V.gram = 1 → Seed.FrmC.StdLat V → UnitFr P → RatIso P e → Formalism.AUTREP.IsAlgWeight D.host.E V.rank (wtRep c e) → (wtRep c e).IsIrreducible → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (S : CSD D.what₂.LL) (act : Representation D.what₂.LL G₀ S.Forms) (pres : Bridge.ClassPres (Bridge.ratF V) S D.what₂.embLL c.coef.ρ (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).J (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).χ) (tie : Bridge.ActTie (Bridge.ratF V) pres (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).Q (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).ch act) (eG : G₀ ≃* G0 Pg D.R.r) (P₀ : Subgroup G₀) (ψ₀ : P₀ →* D.what₂.LLˣ), (∀ q : (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).Q, eG (tie.red q) = rTup 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi) (Formalism.UG.bc (swapAE D) ((q : Bridge.Gf V) : GL _ _))) → ∀ (lam : D.what₂.Tau → DomWeight V.rank) (c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] c.W) pair del, Bridge.CoefMapTie V c.coef c0 (rhoVr (labLL D) lam) → Bridge.CoefTie V c.coef pres lam c0 pair (nabAtr (labLL D) lam) del → (∀ k : (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).J, ∃ z : 𝓞 D.what₂.LL, D.what₂.embLL (z : D.what₂.LL) = ((levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).χ k : ℂ)) → ∀ B, NG.HypOutside (stdJ (datV D V.rank hr Pg Q (levPOf eG D.what₂.embLL P₀ ψ₀) chi xi)) (stdX (datV D V.rank hr Pg Q (levPOf eG D.what₂.embLL P₀ ψ₀) chi xi)) B → ∀ (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)) (k : ℕ), s.v ∉ B → Formalism.AUTREP.IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ V.rank → ∀ x, ∃ x', (fun g => pres.ext (lvlForm S act P₀ ψ₀⁻¹ x').1 (toGf P g)) = NG.tN (stdJ (datV D V.rank hr Pg Q (levPOf eG D.what₂.embLL P₀ ψ₀) chi xi)) s ϖ k (fun g => pres.ext (lvlForm S act P₀ ψ₀⁻¹ x).1 (toGf P g)) ∧ ∀ 𝔴 : HeightOneSpectrum (𝓞 D.what₂.LL), (∀ p : ℕ, p.Prime → s.Above p → (p : 𝓞 D.what₂.LL) ∉ 𝔴.asIdeal) → x ∈ S.lvlNab act P₀ ψ₀⁻¹ → ∃ d : 𝓞 D.what₂.LL, d ∉ 𝔴.asIdeal ∧ d • x' ∈ S.lvlNab act P₀ ψ₀⁻¹ := by
  intro D V hr Pg Q chi xi c P e hg hV hU hR halg hirr G₀ _ _ S act pres tie eG P₀ ψ₀ hred lam c0 pair del hmap hcoef hint
    B hB s ϖ k hs hϖ hk1 hk2 x
  exact tN_core P hg hV hU S act pres tie P₀ ψ₀⁻¹ lam c0 pair del hmap hcoef (hLat_lev V hV _) hint _ _
    (GlobalTheory.T.definiteLevelForms_iff_stdGroupTypeSpace D V hr Pg Q chi xi c P e hg hU hR G₀ tie.red eG P₀ ψ₀ hred) s ϖ k hϖ
    (GlobalTheory.HeckeStdFacts.heckeStdPlain D.host.E V.rank (NG.AlgWt.mk c.W (wtRep c e) halg hirr) _ _ B
      (GlobalTheory.T.stdFrameLevelSubgroup_bounded_open_hyperspecial D V.rank _).2.1 hB s ϖ k hs hϖ hk1 hk2).1 x

end GlobalTheory.MtInHecke

end
