import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsUnitReprOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationLtOneIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalCoefficientChangeCompare
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthQuotientMaximalIdealPowSmulTop

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.PtCore
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions GlobalTheory.SelBaseChange GlobalTheory.BlochKatoBaseChangeLe
open scoped ENNReal

namespace GlobalTheory.SelTwistLe

section Quot

variable (O : Type) [CommRing O] [IsDomain O] (k : ℕ)

def toPi : KOG O k →ₗ[O] (Fin k → KmodO O) :=
  (stdG O (FractionRing O) k).liftQ
    (LinearMap.compLeft (LinearMap.range (Algebra.linearMap O (FractionRing O))).mkQ (Fin k)) (by
      rintro _ ⟨u, rfl⟩
      funext a
      exact (Submodule.Quotient.mk_eq_zero _).2 ⟨u a, rfl⟩)

variable {O k}

theorem toPi_bij : Function.Bijective (toPi O k) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have h : ∀ a, ∃ c, algebraMap O (FractionRing O) c = v a := fun a =>
      (Submodule.Quotient.mk_eq_zero _).1 (congrFun hx a)
    choose u hu using h
    exact (Submodule.Quotient.mk_eq_zero _).2 ⟨u, funext hu⟩
  · intro x
    choose v hv using fun a => Submodule.Quotient.mk_surjective _ (x a)
    exact ⟨Submodule.Quotient.mk v, funext hv⟩

theorem toPi_WKG {Γ : Type} [Group Γ] (M : Γ →* Matrix (Fin k) (Fin k) O) (g : Γ) (x : KOG O k) (a : Fin k) :
    toPi O k (WKG M g x) a = ∑ j, M g a j • toPi O k x j := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change Submodule.mkQ _ (∑ j, algebraMap O (FractionRing O) (M g a j) * v j) =
    ∑ j, M g a j • Submodule.mkQ _ (v j)
  simp only [map_sum, ← Algebra.smul_def, map_smul]

theorem push_WKG {O' : Type} [CommRing O'] [IsDomain O'] (f : O →+* O') (hf : Function.Injective f)
    {Γ Γ' : Type} [Group Γ] [Group Γ']
    (M : Γ →* Matrix (Fin k) (Fin k) O) (M' : Γ' →* Matrix (Fin k) (Fin k) O') (γ : Γ) (γ' : Γ')
    (h : M' γ' = (M γ).map f) (x : KOG O k) :
    pushKO f hf k (WKG M γ x) = WKG M' γ' (pushKO f hf k x) := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change Submodule.Quotient.mk (fun j => fracMap f hf
      (((M γ).map (algebraMap O (FractionRing O))).mulVec v j)) =
    Submodule.Quotient.mk (((M' γ').map (algebraMap O' (FractionRing O'))).mulVec fun j => fracMap f hf (v j))
  congr 1
  funext j
  simp [h, Matrix.mulVec, dotProduct, fracMap_alg]

end Quot

section Span

variable {R Γ A A' : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ]
  [AddCommGroup A] [Module R A] [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousConstSMul R A]
  [AddCommGroup A'] [Module R A'] (ρ : Representation R Γ A)

theorem mem_of_span (F : H1 ρ →ₗ[R] A') (S : Set (Γ → A)) (T : Submodule R A')
    (h : ∀ c ∈ S, ∃ hc : c ∈ Z1 ρ, F (Submodule.Quotient.mk ⟨c, hc⟩) ∈ T) (x : H1 ρ)
    (hx : x ∈ ((Submodule.span R S).comap (Z1 ρ).subtype).map (Submodule.mkQ _)) : F x ∈ T := by
  obtain ⟨z, hz, rfl⟩ := hx
  have key : Submodule.span R S ≤ ((T.comap F).comap (Submodule.mkQ _)).map (Z1 ρ).subtype := by
    refine Submodule.span_le.2 fun c hc => ?_
    obtain ⟨h1, h2⟩ := h c hc
    exact ⟨⟨c, h1⟩, h2, rfl⟩
  obtain ⟨z', hz', e⟩ := key hz
  rw [← Subtype.ext e]
  exact hz'

end Span

section Lift

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
  {O : Type} [CommRing O] [IsDomain O] [Algebra ℤ_[l] O] [TopologicalSpace O] (B : LocBridge l E Ω Gw O)

set_option synthInstance.maxHeartbeats 400000 in

theorem exists_lift {k : ℕ} (M : ↥Gw →* Matrix (Fin k) (Fin k) O) (hM : ∀ a b, Continuous fun g => M g a b)
    (c : ↥(Z1 (WKG M))) (hc : Submodule.Quotient.mk c ∈ Br.bkG B P (WKG M) M) :
    ∃ z ∈ finiteCocycles (P.PD B.Kw) (matRep (Br.locM B M)), ∃ y : ↥Gw → Fin k → FractionRing O,
      (∀ g a, Br.toLLK B (y g a) = z (B.e g) a) ∧ ∀ g, c.1 g = Submodule.Quotient.mk (y g) := by
  obtain ⟨z, hz, m, h⟩ := (mem_HfD_iff P B M _).1 (phi_mem_of_mem_bkG P B M c hc)
  have hcob : cob (matRep (Br.locM B M)) m ∈ finiteCocycles (P.PD B.Kw) (matRep (Br.locM B M)) := by
    refine ⟨⟨?_, fun g h => ?_⟩, m ⊗ₜ 1, fun g => ?_⟩
    · refine continuous_pi fun a => ?_
      change Continuous fun g => (∑ j, ((B.eO (M (B.e.symm g) a j) : Br.Ow B) : Br.LLw B) * m j) - m a
      refine Continuous.sub (continuous_finset_sum _ fun j _ => Continuous.mul ?_ continuous_const)
        continuous_const
      exact continuous_subtype_val.comp (B.eO_cont.comp ((hM a j).comp B.e_symm_cont))
    · simp [cob]
    · simp [cob, actVB, TensorProduct.sub_tmul]
  refine ⟨_, add_mem hz hcob, ?_⟩
  have hy : ∀ g : ↥Gw, ∃ y : Fin k → FractionRing O, (∀ a, Br.toLLK B (y a) =
      (z + cob (matRep (Br.locM B M)) m) (B.e g) a) ∧ c.1 g = Submodule.Quotient.mk y := by
    intro g
    obtain ⟨u, hu⟩ := Submodule.Quotient.mk_surjective _ (c.1 g)
    have hg : Br.phi B k (c.1 (B.e.symm (B.e g))) = _ := h (B.e g)
    rw [MulEquiv.symm_apply_apply, ← hu] at hg
    obtain ⟨n, hn⟩ : Br.vecS B k u - (z (B.e g) + ((Br.locM B M (B.e g)).mulVec m - m)) ∈
      stdG (Br.Ow B) (Br.LLw B) k := (Submodule.Quotient.eq _).1 hg
    refine ⟨fun a => u a - algebraMap O _ (B.eO.symm (n a)), fun a => ?_, ?_⟩
    · have h1 : algebraMap (Br.Ow B) (Br.LLw B) (n a) =
        Br.toLLK B (u a) - (z + cob (matRep (Br.locM B M)) m) (B.e g) a := congrFun hn a
      rw [map_sub, Br.toLLK_alg, RingEquiv.apply_symm_apply, h1, sub_sub_cancel]
    · rw [← hu]
      refine (Submodule.Quotient.eq _).2 ⟨fun a => B.eO.symm (n a), funext fun a => ?_⟩
      simp
  choose y h1 h2 using hy
  exact ⟨y, h1, h2⟩

end Lift

theorem nlen_le_lenN {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (l : ℕ)
    (A A' : Type) [AddCommGroup A] [Module O A] [AddCommGroup A'] [Module O A']
    (h : Module.length O A ≤ Module.length O A') :
    (BlochKatoReduction.Gen.lenN O l A' ≠ ⊤ → nlen (O := O) l A ≠ ⊤) ∧
      ∀ q : ℚ, nlen (O := O) l A = (q : WithTop ℚ) → ENNReal.ofReal (q : ℝ) ≤ BlochKatoReduction.Gen.lenN O l A' := by
  unfold BlochKatoReduction.Gen.lenN nlen
  constructor
  · intro h1
    have h2 : Module.length O A ≠ ⊤ := fun h3 => h1 (by
      rw [(top_le_iff.1 (h3 ▸ h) : Module.length O A' = ⊤), ENat.toENNReal_top, ENNReal.top_div_of_ne_top (ENNReal.natCast_ne_top _)])
    rw [if_neg h2]
    exact WithTop.coe_ne_top
  · intro q hq
    split_ifs at hq with h2
    · exact absurd hq WithTop.top_ne_coe
    · rw [← WithTop.coe_injective hq, lenUnit, GlobalTheory.length_quotient_span_singleton_dvr]
      obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 h2
      rw [← hn] at h ⊢
      generalize (IsDiscreteValuationRing.addVal O (l : O)).toNat = a
      rcases Nat.eq_zero_or_pos a with rfl | ha
      · simp
      · rw [ENat.toNat_coe, Rat.cast_div, Rat.cast_natCast, Rat.cast_natCast,
          ENNReal.ofReal_div_of_pos (by exact_mod_cast ha), ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
        exact ENNReal.div_le_div_right (by simpa using ENat.toENNReal_le.2 h) _

section Main

open Formalism.MainNotions.BlochKatoReduction

variable (D : D7) (i : D.ntw.Tw) (s : D.ntw.Sig i) (k : ℕ) (ψ : Formalism.MainNotions.N.GE D.nd →* (D.ntw.Ok i k)ˣ)

theorem equivariant (g : Formalism.MainNotions.N.GE D.nd) (x : KOG (D.ntw.Ok i k) D.R.r) :
    toPi _ _ (WKG (latTpsi D.ntw i s (toOk D.ntw i k) ψ) g x) = Gen.Trep i s k ψ g (toPi _ _ x) := by
  funext a
  rw [toPi_WKG]
  rw [show toOk D.ntw i k = Gen.phiK D.ntw i k from rfl]
  simp [Gen.Trep, twRep, matAct, latTpsi, latT, twistM, mapM, Gen.chiS, Finset.smul_sum, smul_smul, mul_assoc]

theorem latT_cont (a b : Fin D.R.r) : Continuous fun g => latT D.ntw i s g a b := by
  have h : (fun g => latT D.ntw i s g a b) = fun g =>
      ((D.ntw.chi1 i (D.ntw.jS i s) (D.ntw.side i s) g⁻¹ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) *
        ((D.ntw.rhoS i s g : GL _ _) : Matrix _ _ _) a b := by
    funext g
    simp [latT, twistM]
  rw [h]
  exact ((D.ntw.twistCharacterFamily_continuous i _ _).comp continuous_inv).mul ((D.ntw.rhoS_cont i s).matrix_elem a b)

theorem rep_eq (v : PlE D.host) (hv : v ∈ placesOver D.host.E (D.ntw.l i)) :
    matRep (Br.locM (D.ntwbr i v hv) ((latT D.ntw i s).comp (decS D.nd v))) =
      Gen.repV (bk0 D) i v hv (Gen.Tgl i s) := by
  refine MonoidHom.ext fun g => ?_
  change Matrix.toLinAlgEquiv' _ = Matrix.toLinAlgEquiv' _
  congr 1
  refine Matrix.ext fun a b => ?_
  change (D.ntwbr i v hv).toLL (latT D.ntw i s ((D.ntwbr i v hv).e.symm g).1 a b) =
    (D.ntwbr i v hv).toLL (((Gen.Tgl i s ((D.ntwbr i v hv).e.symm g).1 : GL _ _) : Matrix _ _ _) a b)
  congr 1
  generalize ((D.ntwbr i v hv).e.symm g).1 = γ
  change _ = (Matrix.scalar (Fin D.R.r) ((Gen.chiS i s γ)⁻¹).val * (D.ntw.rhoS i s γ).val :
    Matrix (Fin D.R.r) (Fin D.R.r) (D.ntw.O0 i)) a b
  simp [latT, twistM, Gen.chiS]

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem cond_le (v : PlE D.host) (hv : v ∈ placesOver D.host.E (D.ntw.l i))
    (hψ : ∀ σ ∈ Dec (F := D.host.E) (D.nd.plOm.1 v), ψ σ = 1)
    (x : H1 ((WKG (latTpsi D.ntw i s (toOk D.ntw i k) ψ)).comp (Dec (F := D.host.E) (D.nd.plOm.1 v)).subtype))
    (hx : x ∈ condL D.loc D.ntwbr i s (toOk D.ntw i k) (toOk_inj D.ntw i k) ψ v) :
    cH ((Gen.Trep i s k ψ).comp (Dec (F := D.host.E) (D.nd.plOm.1 v)).subtype)
      ((WKG (latTpsi D.ntw i s (toOk D.ntw i k) ψ)).comp (Dec (F := D.host.E) (D.nd.plOm.1 v)).subtype)
      (toPi _ _) continuous_of_discreteTopology (fun _ _ => equivariant D i s k ψ _ _) x ∈
      Gen.bk (bk0 D) i s k ψ v := by
  unfold condL at hx
  rw [dif_pos hv] at hx
  unfold Gen.bk
  rw [dif_pos hv]
  refine mem_of_span _ _ _ _ ?_ x hx
  rintro _ ⟨c₀, h₀, rfl⟩
  have hM : ∀ g : Gw D.nd v, latTpsi D.ntw i s (toOk D.ntw i k) ψ g.1 =
      (latT D.ntw i s g.1).map (toOk D.ntw i k) := fun g => by
    simp [latTpsi, twistM, mapM, hψ g.1 g.2]
  obtain ⟨z, hz, y, hy, hc⟩ := exists_lift (D.loc (D.ntw.l i)) (D.ntwbr i v hv)
    ((latT D.ntw i s).comp (decS D.nd v)) (fun a b => (latT_cont D i s a b).comp continuous_subtype_val) c₀ h₀
  rw [rep_eq] at hz
  refine ⟨⟨(continuous_of_discreteTopology (f := pushKO _ (toOk_inj D.ntw i k) D.R.r)).comp c₀.2.1,
    fun g h => ?_⟩, Submodule.subset_span
      ⟨_, z, fun g a => fracMap _ (toOk_inj D.ntw i k) (y g a), hz, fun g a => ?_, fun g a => ?_, rfl⟩⟩
  · beta_reduce
    rw [c₀.2.2, map_add]
    exact congrArg _ (push_WKG _ _ (latT D.ntw i s) _ g.1 g.1 (hM g) _)
  · obtain ⟨n, d, hd, e⟩ := IsFractionRing.div_surjective (A := D.ntw.O0 i) (y g a)
    have hd0 := nonZeroDivisors.ne_zero hd
    have e' : algebraMap _ _ d * y g a = algebraMap _ (FractionRing (D.ntw.O0 i)) n := by
      rw [← e, mul_div_cancel₀ _ (by simpa using hd0)]
    refine ⟨n, d, ⟨hd0, ?_⟩, ?_⟩
    · have := congrArg (Br.toLLK (D.ntwbr i v hv)) e'
      rw [map_mul, Br.toLLK_alg, Br.toLLK_alg, hy] at this
      exact this
    · have := congrArg (fracMap _ (toOk_inj D.ntw i k)) e'
      rw [map_mul, fracMap_alg, fracMap_alg] at this
      exact this
  · change toPi _ _ (pushKO _ (toOk_inj D.ntw i k) D.R.r (c₀.1 g)) a = _
    rw [hc]
    rfl

theorem length_le (Q : Finset (PlE D.host))
    (hψ : ∀ v ∈ placesOver D.host.E (D.ntw.l i), ∀ σ ∈ Dec (F := D.host.E) (D.nd.plOm.1 v), ψ σ = 1) :
    Module.length (D.ntw.Ok i k) (selT D.loc D.ntwbr i s Q (toOk D.ntw i k) (toOk_inj D.ntw i k) ψ) ≤
      Module.length (D.ntw.Ok i k) (Gen.selT (bk0 D) i s k Q ψ) := by
  let c := cH (Gen.Trep i s k ψ) (WKG (latTpsi D.ntw i s (toOk D.ntw i k) ψ)) (toPi _ _)
    continuous_of_discreteTopology (equivariant D i s k ψ)
  have hS : setS D.ntw i = Gen.Spl i := by
    ext v
    simp [setS, Gen.Spl]
  have hc : ∀ x ∈ selT D.loc D.ntwbr i s Q (toOk D.ntw i k) (toOk_inj D.ntw i k) ψ,
      c x ∈ Gen.selT (bk0 D) i s k Q ψ := by
    intro x hx
    refine cH_mem_Sel _ _ _ _ _ _ _ _ _ (fun v y hv => ?_) x hx
    rw [hS] at hv
    unfold Formalism.GaloisCohomology.bkCond at hv ⊢
    split_ifs at hv ⊢ with h1 h2
    · exact cond_le D i s k ψ v h1 (hψ v h1) _ hv
    · trivial
    · exact cH_mem_H1ur _ _ _ _ _ _ _ hv
  refine Module.length_le_of_injective (c.restrict hc) ?_
  rw [injective_iff_map_eq_zero]
  intro x hx
  refine Subtype.ext (eq_zero_of_cH (ι := Unit) (Gen.Trep i s k ψ) _ (fun _ => toPi _ _)
    (fun _ => continuous_of_discreteTopology) (fun _ => equivariant D i s k ψ) ⟨?_, ?_⟩ x.1 fun _ => ?_)
  · exact fun m m' h => toPi_bij.1 (congrFun h ())
  · intro m
    obtain ⟨m', hm⟩ := toPi_bij.2 (m ())
    exact ⟨m', funext fun _ => hm⟩
  · exact congrArg Subtype.val hx

end Main

theorem sT_le_sLen : ∀ (D : D7) (i : D.ntw.Tw) (s : D.ntw.Sig i) (k : ℕ) (Q : Finset (PlE D.host)) (ψ : Formalism.MainNotions.N.GE D.nd →* (D.ntw.Ok i k)ˣ), (∀ v ∈ placesOver D.host.E (D.ntw.l i), ∀ σ ∈ Dec (F := D.host.E) (D.nd.plOm.1 v), ψ σ = 1) → (BlochKatoReduction.Gen.sLen (BlochKatoReduction.bk0 D) i s k Q ψ ≠ ⊤ → GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.sT D.loc D.ntwbr i s Q (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.toOk D.ntw i k) (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.toOk_inj D.ntw i k) ψ ≠ ⊤) ∧ ∀ q : ℚ, GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.sT D.loc D.ntwbr i s Q (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.toOk D.ntw i k) (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.toOk_inj D.ntw i k) ψ = (q : WithTop ℚ) → ENNReal.ofReal (q : ℝ) ≤ BlochKatoReduction.Gen.sLen (BlochKatoReduction.bk0 D) i s k Q ψ :=
  fun D i s k Q ψ hψ => nlen_le_lenN _ _ _ (length_le D i s k ψ Q hψ)

end GlobalTheory.SelTwistLe

end
