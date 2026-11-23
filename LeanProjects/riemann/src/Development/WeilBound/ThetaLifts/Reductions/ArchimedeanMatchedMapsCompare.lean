import Development.WeilBound.ThetaLifts.CartanFactorisation.RealTrans
import Development.WeilBound.ThetaLifts.Reductions.JoinDef

noncomputable section

namespace PositivityTheory.ThKF

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKG
open scoped Classical

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {a a' : ℕ} {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

theorem inf_uniq2 (hO : ArchOp) (hL : ArchLie) (hQ : ArchUniq) {n d : ℕ} {Y : Spc F E n}
    {W : Spc F E d} {M : Model σ Y W} {χ χ' : Chr F E} {o : Rep σ Y W} {r s r' s' : ℕ} (hp : IsPair B M χ χ' o r s r' s')
    (hH : PositivityTheory.ThKR.JoinAt B M o) {N N'}
    (h1 : Maximal (fun P => GlobalTheory.Published.ThetaSubInf M B.ψ B.emb o P ∧ P ≠ M.Pol B.ψ B.emb) N)
    (h2 : Maximal (fun P => GlobalTheory.Published.ThetaSubInf M B.ψ B.emb o P ∧ P ≠ M.Pol B.ψ B.emb) N') : N = N' := by
  have H := hH N N' h1.1.1 h2.1.1
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

theorem archimedean_matched_maps_compare (hH : PositivityTheory.ThKR.JoinTri) (hO : ArchOp) (hL : ArchLie) (hQ : ArchUniq) (hC : PolCount)
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
    (fun x hx => (ker_of_eq (inf_uniq2 hO hL hQ p1 (hH F E σ B a a' G X om om' m.triple).1
      (maxInfP hO hL hQ m).1 (maxInfP hO hL hQ m₂).1) x hx).1)
    (ker_of_eq (inf_uniq2 hO hL hQ p2 (hH F E σ B a a' G X om om' m.triple).2
      (maxInfP hO hL hQ m).2 (maxInfP hO hL hQ m₂).2))
    A (fun i x => A' i x) (fun i x => (hA i x).1) (fun i x => (hA' i x).1) (eqv m.real) (eqv m₂.real)
    (fun N hN => m.real.irred N
      (fun γ hγ f hf y e hp => by rw [((hA (.inl ⟨γ, hγ⟩) ⟨f, hf⟩).2 y).1 e]; exact hN _ ⟨f, hf⟩ hp)
      fun k hk f hf y e hp => by rw [((hA (.inr ⟨k, hk⟩) ⟨f, hf⟩).2 y).1 e]; exact hN _ ⟨f, hf⟩ hp)
    (hC F E σ B _ _ _ _ _ _ _ om _ _ _ _ p1)

end PositivityTheory.ThKF

end
