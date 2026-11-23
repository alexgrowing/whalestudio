import Development.WeilBound.ThetaLifts.CartanFactorisation.CommuteConj
import Development.WeilBound.ThetaLifts.CartanFactorisation.Factor
import Development.WeilBound.ThetaLifts.CartanFactorisation.PolCountDef

noncomputable section

namespace PositivityTheory.ThKF

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKG
open scoped Classical

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {a a' : ℕ} {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

theorem ker_of_eq {Q P P₂ : Type} [AddCommGroup Q] [Module ℂ Q] [AddCommGroup P] [Module ℂ P] [AddCommGroup P₂] [Module ℂ P₂]
    {S : Submodule ℂ Q} {p : Q →ₗ[ℂ] P} {p₂ : Q →ₗ[ℂ] P₂} (h : LinearMap.ker p ⊓ S = LinearMap.ker p₂ ⊓ S) :
    ∀ x ∈ S, p x = 0 ↔ p₂ x = 0 := fun x hx =>
  ⟨fun h0 => (h ▸ (⟨h0, hx⟩ : x ∈ LinearMap.ker p ⊓ S) : x ∈ LinearMap.ker p₂ ⊓ S).1,
    fun h0 => (h.symm ▸ (⟨h0, hx⟩ : x ∈ LinearMap.ker p₂ ⊓ S) : x ∈ LinearMap.ker p ⊓ S).1⟩

theorem cmp_fin (hM : MaxFin) {R R₂ : RealMaps F a a'} {Rf Rf₂ : FinMaps F a a'} (m : IsMatched B G X om om' R Rf)
    (v : Pl F) (n₂ : Nontrivial (Rf₂.Pi v)) (o : (SB _).map (Rf₂.p v) = ⊤) (o' : (SB _).map (Rf₂.p' v) = ⊤)
    (x₁ : Maximal (fun P => GlobalTheory.Published.ThetaSub om v P ∧ P ≠ SB _) (LinearMap.ker (Rf₂.p v) ⊓ SB _))
    (x₂ : Maximal (fun P => GlobalTheory.Published.ThetaSub om' v P ∧ P ≠ SB _) (LinearMap.ker (Rf₂.p' v) ⊓ SB _))
    (eq₂ : ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB _, ∀ φ' ∈ SB _, ∀ φ₁ ∈ SB _, ∀ φ₁' ∈ SB _,
      Acts (evFin F v) (om (1, h)) φ φ₁ → Acts (evFin F v) (om' (1, h)) φ' φ₁' →
      Rf₂.p v φ = Rf₂.p' v φ' → Rf₂.p v φ₁ = Rf₂.p' v φ₁') :
    ∃ (e : Rf.Pi v →ₗ[ℂ] Rf₂.Pi v) (c : ℂ), c ≠ 0 ∧ (∀ x ∈ SB _, e (Rf.p v x) = Rf₂.p v x) ∧
      ∀ x ∈ SB _, e (Rf.p' v x) = c • Rf₂.p' v x := by
  have p1 := pairV m.triple
  have p2 := pairV' m.triple
  obtain ⟨ω, ρ, hω⟩ := PositivityTheory.ThKH.Locrep.locRepEx F E σ _ _ B _ _ G.M om
    ⟨p1.base, ⟨_, _, p1.herm⟩, ⟨_, _, p1.skew⟩, p1.good, ⟨_, _, p1.weil⟩⟩ v
  choose A' hA' hA'' using fun (i : UAt σ G.W (evFin F v)) (x : SB (Fin a' × Fin (a + a') → Fv F v)) => ex_fin p2 v i x x.2
  have ac : ∀ (i : UAt σ G.W (evFin F v)) (x : SB (Fin a × Fin (a + a') → Fv F v)),
      Acts (evFin F v) (om (1, i.1)) x (ω (1, i.1) x) := fun i x => (hω.acts 1 (one_at _) i i.2 x x.2 _).2 rfl
  have pr : ∀ (i : UAt σ G.W (evFin F v)) (x : SB (Fin a × Fin (a + a') → Fv F v)), ω (1, i.1) x ∈ SB _ :=
    fun i x => hω.pres 1 (one_at _) i i.2 x x.2
  haveI := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
  haveI : SecondCountableTopology (Fv F v) := inferInstance
  exact schur_match (SB _) (SB _) (Rf.p v) (Rf.p' v) (Rf₂.p v) (Rf₂.p' v) (m.fin.onto v) (m.fin.onto' v) o o'
    (fun x hx => (ker_of_eq (hM F E σ B _ _ _ _ _ _ _ om _ _ _ _ p1 v _ _ (maxFinP m v).1 x₁) x hx).1)
    (ker_of_eq (hM F E σ B _ _ _ _ _ _ _ om' _ _ _ _ p2 v _ _ (maxFinP m v).2 x₂))
    (fun i : UAt σ G.W (evFin F v) => ω (1, i.1) ∘ₗ Submodule.subtype _) A' pr hA'
    (fun i x x' => m.fin.equiv v i i.2 x x.2 x' x'.2 _ (pr i x) _ (hA' i x') (ac i x) (hA'' i x'))
    (fun i x x' => eq₂ i i.2 x x.2 x' x'.2 _ (pr i x) _ (hA' i x') (ac i x) (hA'' i x'))
    (fun N hN => m.fin.irred v N fun h hh x hx y _ e hp => by
      rw [(hω.acts 1 (one_at _) h hh x hx y).1 e]; exact hN ⟨h, hh⟩ ⟨x, hx⟩ hp)
    (rank_SB _)

theorem max_uniq {α : Type} [SemilatticeSup α] {St : α → Prop} {S N N' : α} (hs : St (N ⊔ N'))
    (h : N ≠ S → N' ≠ S → N ⊔ N' ≠ S) (h1 : Maximal (fun P => St P ∧ P ≠ S) N) (h2 : Maximal (fun P => St P ∧ P ≠ S) N') :
    N = N' :=
  le_antisymm (le_sup_left.trans (h2.2 ⟨hs, h h1.1.2 h2.1.2⟩ le_sup_right)) (le_sup_right.trans (h1.2 ⟨hs, h h1.1.2 h2.1.2⟩ le_sup_left))

theorem inf_uniq (hH : GlobalTheory.Published.HoweDualityReal) (hO : ArchOp) (hL : ArchLie) (hQ : ArchUniq) {n d : ℕ} {Y : Spc F E n}
    {W : Spc F E d} {M : Model σ Y W} {χ χ' : Chr F E} {o : Rep σ Y W} {r s r' s' : ℕ} (hp : IsPair B M χ χ' o r s r' s') {N N'}
    (h1 : Maximal (fun P => GlobalTheory.Published.ThetaSubInf M B.ψ B.emb o P ∧ P ≠ M.Pol B.ψ B.emb) N)
    (h2 : Maximal (fun P => GlobalTheory.Published.ThetaSubInf M B.ψ B.emb o P ∧ P ≠ M.Pol B.ψ B.emb) N') : N = N' := by
  have H := (hH F E σ hp.base.cm n d Y W M B.ψ χ χ' o hp.base.std hp.herm.herm (detX hp) hp.skew.skew (detW hp) hp.resX hp.resW
    hp.hX hp.hW hp.weil B.emb hp.herm.cartan hp.skew.cartan).2 N N' h1.1.1 h2.1.1
  obtain ⟨a1, a2, a3, a4, a5⟩ := h1.1.1
  obtain ⟨b1, -, -, b4, b5⟩ := h2.1.1
  have st : ∀ i, ∀ f ∈ N ⊔ N', ∀ y, RInf B o i f y → y ∈ N ⊔ N' := fun i f hf y hy => by
    obtain ⟨A, hA⟩ := exists_linop hO hL hQ hp i
    obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.1 hf
    rw [((hA ⟨u + w, add_mem (a1 hu) (b1 hw)⟩).2 y).1 hy,
      show (⟨u + w, add_mem (a1 hu) (b1 hw)⟩ : M.Pol B.ψ B.emb) = ⟨u, a1 hu⟩ + ⟨w, b1 hw⟩ from rfl, map_add]
    have x1 := ((hA ⟨u, a1 hu⟩).2 _).2 rfl
    have x2 := ((hA ⟨w, b1 hw⟩).2 _).2 rfl
    rcases i with γ | k
    exacts [Submodule.add_mem_sup (a4 γ γ.2 u hu _ x1) (b4 γ γ.2 w hw _ x2),
      Submodule.add_mem_sup (a5 k k.2 u hu _ x1) (b5 k k.2 w hw _ x2)]
  exact max_uniq ⟨sup_le a1 b1, fun γ hγ f hf y e => Submodule.mem_sup_left (a2 γ hγ f hf y e),
    fun k hk f hf y e => Submodule.mem_sup_left (a3 k hk f hf y e), fun γ hγ => st (.inl ⟨γ, hγ⟩), fun k hk => st (.inr ⟨k, hk⟩)⟩
    H h1 h2

theorem cmp_inf (hH : GlobalTheory.Published.HoweDualityReal) (hO : ArchOp) (hL : ArchLie) (hQ : ArchUniq) (hC : PolCount)
    {R R₂ : RealMaps F a a'} {Rf : FinMaps F a a'} (m : IsMatched B G X om om' R Rf) (m₂ : IsMatched B G X om om' R₂ Rf) :
    ∃ (e : R.Pi →ₗ[ℂ] R₂.Pi) (c : ℂ), c ≠ 0 ∧ (∀ x ∈ G.M.Pol B.ψ B.emb, e (R.p x) = R₂.p x) ∧
      ∀ x ∈ G.M'.Pol B.ψ B.emb, e (R.p' x) = c • R₂.p' x := by
  have p1 := pairV m.triple
  have p2 := pairV' m.triple
  choose A hA using exists_linop hO hL hQ p1
  choose A' hA' using exists_linop hO hL hQ p2
  haveI := m₂.real.nontriv
  have eqv : ∀ {R : RealMaps F a a'}, IsRealMaps B G om om' R → ∀ i (x : G.M.Pol B.ψ B.emb) (x' : G.M'.Pol B.ψ B.emb),
      R.p x = R.p' x' → R.p (A i x) = R.p' (A' i x') := fun h i x x' => by
    have x1 := ((hA i x).2 _).2 rfl
    have x2 := ((hA' i x').2 _).2 rfl
    rcases i with γ | k
    exacts [h.lie γ γ.2 x x.2 x' x'.2 _ _ x1 x2, h.cpt k k.2 x x.2 x' x'.2 _ _ x1 x2]
  exact schur_match _ _ R.p R.p' R₂.p R₂.p' m.real.quot.onto m.real.quot'.onto m₂.real.quot.onto m₂.real.quot'.onto
    (fun x hx => (ker_of_eq (inf_uniq hH hO hL hQ p1 (maxInfP hO hL hQ m).1 (maxInfP hO hL hQ m₂).1) x hx).1)
    (ker_of_eq (inf_uniq hH hO hL hQ p2 (maxInfP hO hL hQ m).2 (maxInfP hO hL hQ m₂).2))
    A (fun i x => A' i x) (fun i x => (hA i x).1) (fun i x => (hA' i x).1) (eqv m.real) (eqv m₂.real)
    (fun N hN => m.real.irred N
      (fun γ hγ f hf y e hp => by rw [((hA (.inl ⟨γ, hγ⟩) ⟨f, hf⟩).2 y).1 e]; exact hN _ ⟨f, hf⟩ hp)
      fun k hk f hf y e hp => by rw [((hA (.inr ⟨k, hk⟩) ⟨f, hf⟩).2 y).1 e]; exact hN _ ⟨f, hf⟩ hp)
    (hC F E σ B _ _ _ _ _ _ _ om _ _ _ _ p1)

theorem real_trans (hO : ArchOp) (hL : ArchLie) (hQ : ArchUniq) {R : RealMaps F a a'} {V V' W} (t : IsTriple B G X om om')
    (t₂ : IsTriple B (reG G V V' W) X om om') (r : IsRealMaps B G om om' R) {g g' h T T'} (hg : Moves B G.V V g)
    (hg' : Moves B G.V' V' g') (hh : Moves B G.W W h) (hT : IsArchOp om (g, h) T) (hT' : IsArchOp om' (g', h) T')
    (hP : ((reG G V V' W).M.Pol B.ψ B.emb).map (T : _ →ₗ[ℂ] _) = G.M.Pol B.ψ B.emb)
    (hP' : ((reG G V V' W).M'.Pol B.ψ B.emb).map (T' : _ →ₗ[ℂ] _) = G.M'.Pol B.ψ B.emb) :
    IsRealMaps B (reG G V V' W) om om' ⟨R.Pi, R.p ∘ₗ (T : _ →ₗ[ℂ] _), R.p' ∘ₗ (T' : _ →ₗ[ℂ] _)⟩ := by
  have p1 := pairV t
  have p2 := pairV' t
  have q1 := pairV t₂
  have q2 := pairV' t₂
  refine ⟨quot_trans hO hL hQ p1 q1 hg hT hP r.quot, quot_trans hO hL hQ p2 q2 hg' hT' hP' r.quot',
    fun γ hγ f hf f' hf' f₁ f₁' a1 a2 => r.lie _ (conj_line hh.1 hγ) (T f) (hP ▸ ⟨f, hf, rfl⟩) (T' f') (hP' ▸ ⟨f', hf', rfl⟩) _ _
      (transL hO hL hQ p1 q1 hT hP one_line (conj_line hh.1 hγ) one_line hγ (fun t => cj2 g h (γ t)) hf a1)
      (transL hO hL hQ p2 q2 hT' hP' one_line (conj_line hh.1 hγ) one_line hγ (fun t => cj2 g' h (γ t)) hf' a2),
    fun k hk f hf f' hf' f₁ f₁' a1 a2 => r.cpt _ (hh.up hk) (T f) (hP ▸ ⟨f, hf, rfl⟩) (T' f') (hP' ▸ ⟨f', hf', rfl⟩) _ _
      (transK hO hQ p1 hT (one_at _) (hh.up hk).1 (cj2 g h k) a1) (transK hO hQ p2 hT' (one_at _) (hh.up hk).1 (cj2 g' h k) a2),
    r.nontriv, fun N h1 h2 => r.irred N (fun γ hγ f hf y e hp => ?_) fun k hk f hf y e hp => ?_⟩
  · obtain ⟨u, hu, rfl⟩ : f ∈ ((reG G V V' W).M.Pol B.ψ B.emb).map (T : _ →ₗ[ℂ] _) := hP ▸ hf
    have l := conj_line (re_inv hh.1) hγ
    obtain ⟨z, -, hz⟩ := pol_lie hO hL hQ q1 one_line l hu
    have := transL hO hL hQ p1 q1 hT hP one_line hγ one_line l (fun t => cj3 g h (γ t)) hu ((hz z).2 rfl)
    rw [(hQ F _ _ y (T z)).2 _ e this]
    exact h1 _ l u hu z ((hz z).2 rfl) hp
  · obtain ⟨u, hu, rfl⟩ : f ∈ ((reG G V V' W).M.Pol B.ψ B.emb).map (T : _ →ₗ[ℂ] _) := hP ▸ hf
    have l := hh.down hk
    obtain ⟨z, -, hz⟩ := pol_k hO hQ q1 (one_kinf _) l hu
    have := transK hO hQ p1 hT (one_at _) hk.1 (cj3 g h k) ((hz z).2 rfl)
    rw [(hQ F _ _ y (T z)).1 _ e this]
    exact h2 _ l u hu z ((hz z).2 rfl) hp

theorem I_move (hI : ILeft) {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} {M : Model σ Y W} {χ χ' : Chr F E} {o : Rep σ Y W}
    {r s r' s' : ℕ} (hp : IsPair B M χ χ' o r s r' s') {Φ} (hΦ : Φ ∈ schA F _) (g h x) :
    M.I o (o (g, h) Φ) x = M.I o Φ (x * h) := by
  rw [show (g, h) = ((g, 1) : UA σ Y.J × UA σ W.J) * (1, h) by simp, map_mul, Module.End.mul_apply,
    hI F E σ B n d Y W M χ χ' o r s r' s' hp _ (hp.weil.isUSplitting.pres _ _ hΦ), I_right]

theorem move_sum {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} {M : Model σ Y W} {ψ} (hM : M.IsGood ψ) {o : Rep σ Y W} {x T}
    (hT : IsArchOp o x T) {m : ℕ} (f : Fin m → SInf F (Fin n × Fin d)) (φ : Fin m → ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ)
    (h1 : ∀ i v, φ i v ∈ SB _) (h2 : ∀ i, ∀ᶠ v in cofinite, φ i v = M.vac v) :
    o x (∑ i, pure (f i) (φ i)) = ∑ i, pure (T (f i)) (φ i) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨g, hg, e⟩ := pure_eq_pureA hM (φ i) (h1 i) (h2 i)
  rw [e, e, hT.1 _ g hg]

theorem so_re (V V' W) : G.M'.So B.ψ B.τ₁ ≤ (reG G V V' W).M'.So B.ψ B.τ₁ := by
  refine Submodule.span_mono ?_
  rintro _ ⟨f, φ, h1, h2, ⟨h3, ι, h4, h5⟩, rfl⟩
  exact ⟨f, φ, h1, h2, ⟨h3, ι, ⟨h4.bij, h4.trans, h4.mult⟩, h5⟩, rfl⟩

theorem polRe_of (hH : GlobalTheory.Published.HoweDualityReal) (hM : MaxFin) (hO : ArchOp) (hL : ArchLie) (hQ : ArchUniq) (hC : PolCount)
    (hJ : CartanConj) (hV : CartanMove) (hK : KCoinv) (hI : ILeft) : PolRe := by
  rintro F E _ _ _ _ _ σ B a a' G X om om' R Rf m V V' W R₂ Rf₂ m₂ ⟨c₂, hc₂, hc⟩
  have p1 := pairV m.triple
  have p2 := pairV' m.triple
  obtain ⟨h, hh, hh'⟩ := hJ F E σ B _ G.W W _ _ p1.base p1.skew m₂.triple.geo.hW
  obtain ⟨g, hg, hg', hP⟩ := hV F E σ B _ _ _ _ _ _ _ om _ _ _ _ p1 V W (reG G V V' W).M rfl (pairV m₂.triple) h hh hh'
  obtain ⟨g', hk, hk', hP'⟩ := hV F E σ B _ _ _ _ _ _ _ om' _ _ _ _ p2 V' W (reG G V V' W).M' rfl (pairV' m₂.triple) h hh hh'
  obtain ⟨T, hT, -⟩ := hO F E σ B _ _ _ _ _ _ _ om _ _ _ _ p1 g hg h hh
  obtain ⟨T', hT', -⟩ := hO F E σ B _ _ _ _ _ _ _ om' _ _ _ _ p2 g' hk h hh
  obtain ⟨e, c, c0, he, he'⟩ := cmp_inf hH hO hL hQ hC ⟨m₂.triple, real_trans hO hL hQ m.triple m₂.triple m.real ⟨hg, hg'⟩ ⟨hk, hk'⟩
    ⟨hh, hh'⟩ hT hT' (hP T hT) (hP' T' hT'), m₂.fin⟩ m₂
  choose ef cf cf0 hef hef' using fun v => cmp_fin (R₂ := R₂) hM m v (m₂.fin.nontriv v) (m₂.fin.onto v) (m₂.fin.onto' v)
    (maxFinP m₂ v).1 (maxFinP m₂ v).2 (m₂.fin.equiv v)
  have cf1 : ∀ v ∉ X.T, cf v = 1 := fun v hv => by
    obtain ⟨s1, s2⟩ := m₂.fin.sph v hv
    have x1 := hef v _ (p1.good.vac v).1
    rw [(m.fin.sph v hv).1, hef' v _ (p2.good.vac v).1] at x1
    have x2 : cf v • Rf₂.p v (G.M.vac v) = (1 : ℂ) • Rf₂.p v (G.M.vac v) := by
      rw [one_smul]; exact (congrArg (cf v • ·) s1).trans x1
    exact smul_left_injective ℂ s2 x2
  let Λ : ℂ := c * ∏ v ∈ X.T, cf v
  refine ⟨c₂ * Λ, mul_ne_zero hc₂ (mul_ne_zero c0 (Finset.prod_ne_zero_iff.2 fun v _ => cf0 v)), ?_⟩
  rintro Φ Φ' hΦ' ⟨S, hS, k, k', f, φ, f', φ', h1, h2, rfl, rfl, eq⟩ x
  choose u hu hu' using fun i => (show f i ∈ ((reG G V V' W).M.Pol B.ψ B.emb).map (T : _ →ₗ[ℂ] _) from hP T hT ▸ (h1 i).1)
  choose u' hw hw' using fun i => (show f' i ∈ ((reG G V V' W).M'.Pol B.ψ B.emb).map (T' : _ →ₗ[ℂ] _) from hP' T' hT' ▸ (h2 i).1)
  have e1 := move_sum p1.good hT u φ (fun i => (h1 i).2.1) fun i => ev_of_off (h1 i).2.2
  have e2 := move_sum p2.good hT' u' φ' (fun i => (h2 i).2.1) fun i => ev_of_off (h2 i).2.2
  have fu : ∀ i, T (u i) = f i := hu'
  have fu' : ∀ i, T' (u' i) = f' i := hw'
  simp only [fu] at e1
  simp only [fu'] at e2
  have s1 : ∑ i, pure (u i) (φ i) ∈ schA F _ := sum_mem fun i _ =>
    GlobalTheory.TensUniq.pure_mem_schA _ _ (h1 i).2.1 ((good_std p1.good).congr (ev_of_off (h1 i).2.2))
  have so : ∑ i, pure (u' i) (φ' i) ∈ G.M'.So B.ψ B.τ₁ := by
    have := (hK F E σ B a a' G X om om' R Rf m).2 (g', h)⁻¹ _ hΦ'
    rwa [← e2, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at this
  have e3 : Λ • ∑ i, pure (u' i) (φ' i) = ∑ i, pure (Λ • u' i) (φ' i) := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => funext fun y => (mul_assoc _ _ _).symm
  have pm : PolMatch B (reG G V V' W) X R₂ Rf₂ (∑ i, pure (u i) (φ i)) (Λ • ∑ i, pure (u' i) (φ' i)) := by
    refine ⟨S, hS, k, k', u, φ, fun i => Λ • u' i, φ', fun i => ⟨hu i, (h1 i).2⟩,
      fun i => ⟨Submodule.smul_mem _ _ (hw i), (h2 i).2⟩, rfl, e3, ?_⟩
    have := congrArg (TensorProduct.map e (PiTensorProduct.map fun v : S => ef v)) eq
    simp only [map_sum, TensorProduct.map_tmul, PiTensorProduct.map_tprod] at this
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) (this.trans (Finset.sum_congr rfl fun j _ => ?_))
    · rw [← fu i, show e (R.p (T (u i))) = R₂.p (u i) from he _ (hu i)]
      simp only [hef _ _ ((h1 i).2.1 _)]
    · rw [← fu' j, show e (R.p' (T' (u' j))) = c • R₂.p' (u' j) from he' _ (hw j)]
      simp only [hef' _ _ ((h2 j).2.1 _)]
      rw [MultilinearMap.map_smul_univ, TensorProduct.smul_tmul_smul, map_smul, TensorProduct.smul_tmul',
        Finset.prod_coe_sort S cf, ← Finset.prod_subset hS fun v _ hv => cf1 v hv]
  have := hc _ _ (Submodule.smul_mem _ Λ (so_re V V' W so)) pm (x * h)
  rw [← e1, ← e2, I_move hI p1 s1, I_move hI p2 (so_le p2.good _ so), mul_assoc, ← I_smul]
  exact this

end PositivityTheory.ThKF

end
