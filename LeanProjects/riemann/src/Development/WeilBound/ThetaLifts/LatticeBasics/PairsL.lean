import Development.WeilBound.ThetaLifts.LatticeBasics.PairsStable
import Development.WeilBound.ThetaLifts.LatticeBasics.PairsD
import Development.WeilBound.ThetaLifts.ConeHypotheses.PureEqPureA
import Development.WeilBound.ThetaLifts.CartanFactorisation.CartanConj
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.InertDef

noncomputable section

namespace GlobalTheory.ThK.Dbl.Prs

open scoped TensorProduct Classical
open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl.Dens
open PositivityTheory.ThKF (ArchOp PureAct)
open PositivityTheory.ThK (LocRepEx)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' n d : ℕ}
  {Y : Spc F E n} {W : Spc F E d} {B : Base F E} {M : Model σ Y W} {o : Rep σ Y W} {R : RealMaps F a a'} {Rf : FinMaps F a a'}
  {p : SInf F (Fin n × Fin d) →ₗ[ℂ] R.Pi} {q : ∀ v, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] Rf.Pi v} {T T₁ : Finset (Pl F)}

variable (R Rf T) in

abbrev PiT : Type := R.Pi ⊗[ℂ] PiTensorProduct ℂ fun v : T => Rf.Pi v

variable (B M T) in

def Dat (f : SInf F (Fin n × Fin d)) (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ) : Prop :=
  f ∈ M.Pol B.ψ B.emb ∧ (∀ v, φ v ∈ SB _) ∧ ∀ v ∉ T, φ v = M.vac v

variable (B M p q T) in

def Cl : Submodule ℂ (Fn F n d × PiT R Rf T) :=
  Submodule.span ℂ {z | ∃ f φ, Dat B M T f φ ∧ z = (pure f φ, p f ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ fun v : T => q v (φ v))}

theorem Dat.cof {f φ} (h : Dat B M T f φ) : ∀ᶠ v in cofinite, φ v = M.vac v :=
  T.eventually_cofinite_notMem.mono h.2.2

theorem Dat.pureA (hM : M.IsGood B.ψ) {f φ} (h : Dat B M T f φ) :
    ∃ g ∈ SB (Fin n × Fin d → Af F), ∀ f' : SInf F (Fin n × Fin d), pure f' φ = pureA F f' g :=
  PositivityTheory.ThKG.pure_eq_pureA hM φ h.2.1 h.cof

theorem Dat.sch (hM : M.IsGood B.ψ) {f φ} (h : Dat B M T f φ) : pure f φ ∈ schA F _ := by
  obtain ⟨g, hg, e⟩ := h.pureA hM
  exact Submodule.subset_span ⟨f, g, hg, e f⟩

theorem gen_mem {f φ} (h : Dat B M T f φ) :
    (pure f φ, p f ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ fun v : T => q v (φ v)) ∈ Cl B M p q T := Submodule.subset_span ⟨f, φ, h, rfl⟩

theorem mem_cl {Φ ξ} : (Φ, ξ) ∈ Cl B M p q T ↔ ∃ (m : ℕ) (f : Fin m → SInf F _) (φ : Fin m → ∀ v : Pl F, (_ → Fv F v) → ℂ),
    (∀ i, Dat B M T (f i) (φ i)) ∧ Φ = ∑ i, pure (f i) (φ i) ∧
      ξ = ∑ i, p (f i) ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ fun v : T => q v (φ i v) := by
  constructor
  · intro h
    obtain ⟨m, c, g, e⟩ := Submodule.mem_span_set'.1 h
    choose f φ hd hg using fun i => (g i).2
    have e1 : ∀ i, pure (c i • f i) (φ i) = c i • pure (f i) (φ i) := fun i => funext fun x => by
      simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]
    refine ⟨m, fun i => c i • f i, φ, fun i => ⟨Submodule.smul_mem _ _ (hd i).1, (hd i).2⟩, ?_, ?_⟩
    · simpa [hg, e1, Prod.fst_sum] using (congrArg Prod.fst e).symm
    · simpa [hg, Prod.snd_sum, TensorProduct.smul_tmul'] using (congrArg Prod.snd e).symm
  · rintro ⟨m, f, φ, hd, rfl, rfl⟩
    rw [prod_mk_sum]
    exact Submodule.sum_mem _ fun i _ => gen_mem (hd i)

theorem cl_map (A : Fn F n d →ₗ[ℂ] Fn F n d) (Ω : PiT R Rf T →ₗ[ℂ] PiT R Rf T₁)
    (h : ∀ f φ, Dat B M T f φ →
      (A (pure f φ), Ω (p f ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ fun v : T => q v (φ v))) ∈ Cl B M p q T₁)
    {Φ ξ} (hz : (Φ, ξ) ∈ Cl B M p q T) : (A Φ, Ω ξ) ∈ Cl B M p q T₁ :=
  (Submodule.span_le (p := (Cl B M p q T₁).comap (A.prodMap Ω))).2 (by rintro _ ⟨f, φ, hd, rfl⟩; exact h f φ hd) hz

theorem cl_ext (hT : T ⊆ T₁) (e : (PiTensorProduct ℂ fun v : T => Rf.Pi v) →ₗ[ℂ] PiTensorProduct ℂ fun v : T₁ => Rf.Pi v)
    (s : ∀ v, Rf.Pi v) (he : ∀ u : ∀ v, Rf.Pi v, (∀ v ∉ T, u v = s v) →
      e (PiTensorProduct.tprod ℂ fun v : T => u v) = PiTensorProduct.tprod ℂ fun v : T₁ => u v)
    (hs : ∀ v ∉ T, q v (M.vac v) = s v) {Φ ξ} (hz : (Φ, ξ) ∈ Cl B M p q T) : (Φ, e.lTensor _ ξ) ∈ Cl B M p q T₁ :=
  cl_map LinearMap.id _ (fun f φ hd => by
    rw [LinearMap.lTensor_tmul, he (fun v => q v (φ v)) fun v hv => by rw [hd.2.2 v hv, hs v hv]]
    exact gen_mem ⟨hd.1, hd.2.1, fun v hv => hd.2.2 v fun h => hv (hT h)⟩) hz

variable (R) in

def opAt (v : T) (Op : Module.End ℂ (Rf.Pi v)) : PiT R Rf T →ₗ[ℂ] PiT R Rf T :=
  LinearMap.lTensor R.Pi (PiTensorProduct.map (Function.update (fun j : T => (LinearMap.id : Rf.Pi j →ₗ[ℂ] Rf.Pi j)) v Op))

theorem cl_fin (hP : PureAct) (hM : M.IsGood B.ψ) (v : T) (A : Fn F n d →ₗ[ℂ] Fn F n d) (Op : Module.End ℂ (Rf.Pi v))
    (h : ∀ φ ∈ SB _, ∃ φ₁ ∈ SB _, Acts (evFin F v) A φ φ₁ ∧ Op (q v φ) = q v φ₁) {Φ ξ} (hz : (Φ, ξ) ∈ Cl B M p q T) :
    (A Φ, opAt R v Op ξ) ∈ Cl B M p q T := by
  refine cl_map A _ (fun f φ hd => ?_) hz
  obtain ⟨φ₁, s1, a1, e1⟩ := h _ (hd.2.1 v)
  have d₂ : Dat B M T f (Function.update φ v φ₁) := by
    refine ⟨hd.1, fun w => ?_, fun w hw => ?_⟩
    · by_cases hw : w = v
      · subst hw; simpa using s1
      · simpa [Function.update_of_ne hw] using hd.2.1 w
    · rw [Function.update_of_ne (fun e : w = v => hw (by rw [e]; exact v.2)), hd.2.2 w hw]
  convert gen_mem (p := p) (q := q) d₂ using 2
  · exact (hP F _ v A f φ hd.2.1 ((hd.cof.and hM.std).mono fun _ k => k.1.trans k.2)).2.2 _ a1
  · simp only [opAt, LinearMap.lTensor_tmul, PiTensorProduct.map_tprod]
    congr 2
    funext w
    by_cases hw : w = v
    · subst hw; simpa using e1
    · simp [Function.update_of_ne hw, Function.update_of_ne (show (w : Pl F) ≠ v from fun e => hw (Subtype.ext e))]

def finPart {κ : Type} (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) (x : κ → AF F) : ℂ := ∏ᶠ v, φ v fun i => evFin F v (x i)

theorem finPart_add {κ : Type} (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) (x z : κ → AF F) (hz : At (evI F) z) :
    finPart φ (x + z) = finPart φ x := by
  have e : ∀ (v : Pl F) i, evFin F v ((x + z) i) = evFin F v (x i) := fun v i => by
    have h : (1 : Af F) * (z i).2 = 0 :=
      congrArg Prod.snd (congrFun (hz ((0, 1) : Ainf F × Af F) (map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F))) i)
    have h3 : evFin F v (z i) = 0 := by
      show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (z i).2 = 0
      rw [← one_mul (z i).2, h, map_zero]
    rw [Pi.add_apply, map_add, h3, add_zero]
  simp only [finPart, e]

theorem Dat.rest (hM : M.IsGood B.ψ) {f φ} (h : Dat B M T f φ) : Rest (evI F) f (finPart φ) := ⟨finPart_add φ, h.sch hM⟩

theorem cl_inf (hM : M.IsGood B.ψ) (A : Fn F n d →ₗ[ℂ] Fn F n d) (Op : Module.End ℂ R.Pi)
    (h : ∀ f ∈ M.Pol B.ψ B.emb, ∃ f₁ ∈ M.Pol B.ψ B.emb, Acts (evI F) A f f₁ ∧ Op (p f) = p f₁) {Φ ξ}
    (hz : (Φ, ξ) ∈ Cl B M p q T) : (A Φ, Op.rTensor _ ξ) ∈ Cl B M p q T := by
  refine cl_map A _ (fun f φ hd => ?_) hz
  obtain ⟨f₁, s1, a1, e1⟩ := h _ hd.1
  rw [LinearMap.rTensor_tmul, e1, show A (pure f φ) = pure f₁ φ from a1 _ (hd.rest hM)]
  exact gen_mem ⟨s1, hd.2⟩

theorem loc_op (hL : LocRepEx) {χ χ' r s r' s'} (hp : IsPair B M χ χ' o r s r' s') {v : Pl F} {h : UA σ W.J}
    (hh : h ∈ UAt σ W (evFin F v)) : ∃ A : Module.End ℂ ((Fin n × Fin d → Fv F v) → ℂ),
      ∀ φ ∈ SB _, A φ ∈ SB _ ∧ Acts (evFin F v) (o (1, h)) φ (A φ) := by
  obtain ⟨ω, ρ, L⟩ := hL F E σ n d B Y W M o ⟨hp.base, ⟨_, _, hp.herm⟩, ⟨_, _, hp.skew⟩, hp.good, _, _, hp.weil⟩ v
  have o1 : (1 : UA σ Y.J) ∈ UAt σ Y (evFin F v) := fun u _ => by rw [show mat (1 : UA σ Y.J) = 1 from rfl, sub_self, smul_zero]
  exact ⟨ω (1, h), fun φ hφ => ⟨L.pres 1 o1 h hh _ hφ, (L.acts 1 o1 h hh _ hφ _).2 rfl⟩⟩

theorem inf_op (hA : ArchOp) {χ χ' r s r' s'} (hp : IsPair B M χ χ' o r s r' s') {k : UA σ W.J} (hk : k ∈ KInf σ W B.emb) :
    ∃ A : Module.End ℂ (SInf F (Fin n × Fin d)), ∀ f ∈ M.Pol B.ψ B.emb, A f ∈ M.Pol B.ψ B.emb ∧ Acts (evI F) (o (1, k)) f (A f) := by
  have o1 : (1 : UA σ Y.J) ∈ KInf σ Y B.emb :=
    ⟨fun u _ => by rw [show mat (1 : UA σ Y.J) = 1 from rfl, sub_self, smul_zero], fun w => by
      rw [show mat (1 : UA σ Y.J) = 1 from rfl, Matrix.map_one _ (map_zero _) (map_one _)]; exact Commute.one_left _⟩
  obtain ⟨A, a1, a2⟩ := hA F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hp 1 o1.1 k hk.1
  exact ⟨A, fun f hf => ⟨a2 o1 hk f hf, a1.2 f⟩⟩

theorem common_op {V V' P : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] [AddCommGroup P] [Module ℂ P]
    {S : Submodule ℂ V} {S' : Submodule ℂ V'} {p : V →ₗ[ℂ] P} {p' : V' →ₗ[ℂ] P} (h : S.map p = ⊤) (A : S →ₗ[ℂ] V)
    (A' : S' →ₗ[ℂ] V') (e : ∀ x x', p x.1 = p' x'.1 → p (A x) = p' (A' x')) :
    ∃ Op : Module.End ℂ P, (∀ x, Op (p x.1) = p (A x)) ∧ ∀ x', Op (p' x'.1) = p' (A' x') := by
  have hq : Function.Surjective (p.domRestrict S) := fun u => by
    obtain ⟨x, h1, h2⟩ : u ∈ S.map p := h ▸ Submodule.mem_top
    exact ⟨⟨x, h1⟩, h2⟩
  obtain ⟨s, hs⟩ := (p.domRestrict S).exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hq)
  have k : ∀ x : S, p (A (s (p x.1))) = p (A x) := fun x => by
    have := e (s (p x.1) - x) 0 (by simpa [sub_eq_zero] using LinearMap.congr_fun hs (p x.1))
    simpa [sub_eq_zero] using this
  exact ⟨p ∘ₗ A ∘ₗ s, k, fun x' => e _ _ (LinearMap.congr_fun hs _)⟩

variable {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

theorem fin_ops (hL : LocRepEx) (hm : IsMatched B G X om om' R Rf) {v : Pl F} {h : UA σ G.W.J} (hh : h ∈ UAt σ G.W (evFin F v)) :
    ∃ Op : Module.End ℂ (Rf.Pi v), (∀ φ ∈ SB _, ∃ φ₁ ∈ SB _, Acts (evFin F v) (om (1, h)) φ φ₁ ∧ Op (Rf.p v φ) = Rf.p v φ₁) ∧
      (∀ φ ∈ SB _, ∀ φ₁ ∈ SB _, Acts (evFin F v) (om (1, h)) φ φ₁ → Op (Rf.p v φ) = Rf.p v φ₁) ∧
      ∀ φ ∈ SB _, ∃ φ₁ ∈ SB _, Acts (evFin F v) (om' (1, h)) φ φ₁ ∧ Op (Rf.p' v φ) = Rf.p' v φ₁ := by
  obtain ⟨A, hA⟩ := loc_op hL (PositivityTheory.ThKG.pairV hm.triple) hh
  obtain ⟨A', hA'⟩ := loc_op hL (PositivityTheory.ThKG.pairV' hm.triple) hh
  obtain ⟨Op, h1, h2⟩ := common_op (hm.fin.onto v) (A.domRestrict _) (A'.domRestrict (SB _)) fun x x' e =>
    hm.fin.equiv v h hh _ x.2 _ x'.2 _ (hA _ x.2).1 _ (hA' _ x'.2).1 (hA _ x.2).2 (hA' _ x'.2).2 e
  refine ⟨Op, fun φ hφ => ⟨_, (hA _ hφ).1, (hA _ hφ).2, h1 ⟨φ, hφ⟩⟩, fun φ hφ φ₁ h₁ e => ?_,
    fun φ hφ => ⟨_, (hA' _ hφ).1, (hA' _ hφ).2, h2 ⟨φ, hφ⟩⟩⟩
  obtain ⟨φ', s', e'⟩ : Rf.p v φ ∈ (SB _).map (Rf.p' v) := hm.fin.onto' v ▸ Submodule.mem_top
  rw [hm.fin.equiv v h hh _ hφ _ s' _ h₁ _ (hA' _ s').1 e (hA' _ s').2 e'.symm, ← e']
  exact h2 ⟨φ', s'⟩

theorem inf_ops (hO : ArchOp) (hm : IsMatched B G X om om' R Rf) {k : UA σ G.W.J} (hk : k ∈ KInf σ G.W B.emb) :
    ∃ Op : Module.End ℂ R.Pi,
      (∀ f ∈ G.M.Pol B.ψ B.emb, ∃ f₁ ∈ G.M.Pol B.ψ B.emb, Acts (evI F) (om (1, k)) f f₁ ∧ Op (R.p f) = R.p f₁) ∧
      (∀ f ∈ G.M.Pol B.ψ B.emb, ∀ f₁ : SInf F _, Acts (evI F) (om (1, k)) f f₁ → Op (R.p f) = R.p f₁) ∧
      ∀ f ∈ G.M'.Pol B.ψ B.emb, ∃ f₁ ∈ G.M'.Pol B.ψ B.emb, Acts (evI F) (om' (1, k)) f f₁ ∧ Op (R.p' f) = R.p' f₁ := by
  obtain ⟨A, hA⟩ := inf_op hO (PositivityTheory.ThKG.pairV hm.triple) hk
  obtain ⟨A', hA'⟩ := inf_op hO (PositivityTheory.ThKG.pairV' hm.triple) hk
  obtain ⟨Op, h1, h2⟩ := common_op hm.real.quot.onto (A.domRestrict _) (A'.domRestrict (G.M'.Pol B.ψ B.emb)) fun x x' e =>
    hm.real.cpt k hk _ x.2 _ x'.2 _ _ (hA _ x.2).2 (hA' _ x'.2).2 e
  refine ⟨Op, fun f hf => ⟨_, (hA _ hf).1, (hA _ hf).2, h1 ⟨f, hf⟩⟩, fun f hf f₁ e => ?_,
    fun f hf => ⟨_, (hA' _ hf).1, (hA' _ hf).2, h2 ⟨f, hf⟩⟩⟩
  obtain ⟨f', s', e'⟩ : R.p f ∈ (G.M'.Pol B.ψ B.emb).map R.p' := hm.real.quot'.onto ▸ Submodule.mem_top
  rw [hm.real.cpt k hk _ hf _ s' _ _ e (hA' _ s').2 e'.symm, ← e']
  exact h2 ⟨f', s'⟩

theorem polMatch_iff {Φ Φ'} : PolMatch B G X R Rf Φ Φ' ↔
    ∃ T, X.T ⊆ T ∧ ∃ ξ, (Φ, ξ) ∈ Cl B G.M R.p Rf.p T ∧ (Φ', ξ) ∈ Cl B G.M' R.p' Rf.p' T := by
  refine exists_congr fun T => and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨m, m', f, φ, f', φ', h1, h2, e1, e2, e3⟩
    exact ⟨_, mem_cl.2 ⟨m, f, φ, h1, e1, rfl⟩, mem_cl.2 ⟨m', f', φ', h2, e2, e3⟩⟩
  · rintro ⟨ξ, h, h'⟩
    obtain ⟨m, f, φ, h1, e1, e3⟩ := mem_cl.1 h
    obtain ⟨m', f', φ', h2, e2, e4⟩ := mem_cl.1 h'
    exact ⟨m, m', f, φ, f', φ', h1, h2, e1, e2, e3.symm.trans e4⟩

theorem enlarge (hm : IsMatched B G X om om' R Rf) (hX : X.T ⊆ T) (hT : T ⊆ T₁) : ∃ e : PiT R Rf T →ₗ[ℂ] PiT R Rf T₁,
    (∀ Φ ξ, (Φ, ξ) ∈ Cl B G.M R.p Rf.p T → (Φ, e ξ) ∈ Cl B G.M R.p Rf.p T₁) ∧
      ∀ Φ ξ, (Φ, ξ) ∈ Cl B G.M' R.p' Rf.p' T → (Φ, e ξ) ∈ Cl B G.M' R.p' Rf.p' T₁ := by
  obtain ⟨e, he⟩ := exists_ext (X := Rf.Pi) T T₁ hT fun v => Rf.p v (G.M.vac v)
  exact ⟨_, fun _ _ => cl_ext hT e _ he fun _ _ => rfl,
    fun _ _ => cl_ext hT e _ he fun v hv => (hm.fin.sph v fun h => hv (hX h)).1.symm⟩

theorem polMatch_big (hm : IsMatched B G X om om' R Rf) {Φ Φ'} (h : PolMatch B G X R Rf Φ Φ') :
    ∃ T₀, X.T ⊆ T₀ ∧ ∀ T, T₀ ⊆ T → ∃ ξ, (Φ, ξ) ∈ Cl B G.M R.p Rf.p T ∧ (Φ', ξ) ∈ Cl B G.M' R.p' Rf.p' T := by
  obtain ⟨T₀, hT, ξ, h1, h2⟩ := polMatch_iff.1 h
  refine ⟨T₀, hT, fun T h0 => ?_⟩
  obtain ⟨e, e1, e2⟩ := enlarge hm hT h0
  exact ⟨_, e1 _ _ h1, e2 _ _ h2⟩

theorem polMatch_add_smul (hm : IsMatched B G X om om' R Rf) {Φ Φ' Ψ Ψ'} (h : PolMatch B G X R Rf Φ Φ')
    (h' : PolMatch B G X R Rf Ψ Ψ') (c : ℂ) : PolMatch B G X R Rf (Φ + c • Ψ) (Φ' + c • Ψ') := by
  obtain ⟨T, hT, H⟩ := polMatch_big hm h
  obtain ⟨T', -, H'⟩ := polMatch_big hm h'
  obtain ⟨ξ, h1, h2⟩ := H _ (Finset.subset_union_left (s₂ := T'))
  obtain ⟨η, h3, h4⟩ := H' _ (Finset.subset_union_right (s₁ := T))
  exact polMatch_iff.2 ⟨_, hT.trans Finset.subset_union_left, ξ + c • η, add_mem h1 (Submodule.smul_mem _ c h3),
    add_mem h2 (Submodule.smul_mem _ c h4)⟩

end GlobalTheory.ThK.Dbl.Prs

end
