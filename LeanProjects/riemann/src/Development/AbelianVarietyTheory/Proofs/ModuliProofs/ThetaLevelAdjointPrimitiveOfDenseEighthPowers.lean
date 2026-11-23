import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LineBundleTrivialIsoDescendField
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EighthPowerIntegerMatrixPrimitiveAdjoint
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AdjointEndomorphismsCubeLBOfDenseFibresStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LbIsoCubeGraphOfDenseFibresStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.SharpAdjoint

section Bundles

variable {X X' Y Y' : Scheme.{0}}

theorem iso_linComb_pull {L : LB X} {L' : LB X'} {F : X' ⟶ X} (H : LBIso L' (L.pull F)) {K : Type} [Fintype K]
    (ψ' : K → (Y' ⟶ X')) (ψ : K → (Y ⟶ X)) (ε : K → ℤ) (h : Y' ⟶ Y) (e : ∀ k, ψ' k ≫ F = h ≫ ψ k) :
    LBIso (LB.LinComb L' ψ' ε) ((LB.LinComb L ψ ε).pull h) := by
  obtain ⟨w, hw⟩ := H
  exact LBIso.chartPull (chartPullId _) (chartPullOut L ψ ε h _ e) (iso_linComb ((isGen_iff w).1 hw) ψ' ε)

theorem iso_up {M N : LB Y} {M' N' : LB Y'} {h : Y' ⟶ Y} (hM : M.IsLB) (hN : N.IsLB) (hM' : M'.IsLB) (hN' : N'.IsLB)
    (a : LBIso M' (M.pull h)) (b : LBIso N' (N.pull h)) (H : LBIso M N) : LBIso M' N' :=
  LBIso.trans hM' (pull_isLB hM h) hN' a (LBIso.trans (pull_isLB hM h) (pull_isLB hN h) hN'
    (H.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull M h h rfl) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull N h h rfl)) b.symm)

end Bundles

section Field

variable {K : Type} [Field K] {S' : Scheme.{0}} (f : S' ⟶ Sp K)

theorem exists_point [Nonempty S'] :
    ∃ (K' : Type) (_ : Field K') (i : K →+* K') (x : Sp K' ⟶ S'), x ≫ f = spMap i := by
  obtain ⟨y⟩ := ‹Nonempty S'›
  obtain ⟨i, hi⟩ := Spec.map_surjective (S'.fromSpecResidueField y ≫ f)
  exact ⟨S'.residueField y, inferInstance, i.hom, S'.fromSpecResidueField y, hi.symm⟩

variable {f}

theorem iso_down [Nonempty S'] {X₀ X : Scheme.{0}} {p₀ : X₀ ⟶ Sp K} {p : X ⟶ S'} {h : X ⟶ X₀}
    (H : IsPullback h p p₀ f) (h₁ : Smooth p₀) (h₂ : IsProper p₀) (h₃ : GeometricallyConnected p₀)
    {M N : LB X₀} {M' N' : LB X} (hM : M.IsLB) (hN : N.IsLB) (hM' : M'.IsLB) (hN' : N'.IsLB)
    (a : LBIso M' (M.pull h)) (b : LBIso N' (N.pull h)) (c : LBIso M' N') : LBIso M N := by
  obtain ⟨K', _, i, x, hx⟩ := exists_point f
  have P : IsPullback (pullback.fst p x ≫ h) (pullback.snd p x) p₀ (spMap i) :=
    hx ▸ (IsPullback.of_hasPullback p x).paste_horiz H
  have d : LBIso (M.pull h) (N.pull h) := LBIso.trans (pull_isLB hM h) hM' (pull_isLB hN h) a.symm
    (LBIso.trans hM' hN' (pull_isLB hN h) c b)
  exact (GlobalTheory.lb_gen_iso_descend_field K K' i X₀ _ p₀ _ _ h₁ h₂ h₃ P).2 M N hM hN (d.chartPull
    (chartPullSame M _ _ _ (pullback.fst p x) fun _ => rfl) (chartPullSame N _ _ _ (pullback.fst p x) fun _ => rfl))

end Field

section Group

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}
  (h : IsGrpPullback G' G f φ)

section Points

variable {T : Over S} {T' : Over S'} (U : Over.mk (T'.hom ≫ f) ⟶ T)

theorem push_comp {x' : T' ⟶ G'} {x : T ⟶ G} (hx : pushPt h.1.w x' = U ≫ x) {a' : G' ⟶ G'} {a : G ⟶ G}
    (ha : a'.left ≫ φ = φ ≫ a.left) : pushPt h.1.w (x' ≫ a') = U ≫ x ≫ a := by
  rw [← Category.assoc, ← hx]
  refine Over.OverMorphism.ext ?_
  show (x'.left ≫ _) ≫ _ = (x'.left ≫ _) ≫ _
  rw [Category.assoc, ha, Category.assoc]

theorem iso_cubeLB_pull [IsCommMonObj G] [IsCommMonObj G'] {L : LB G.left} {L' : LB G'.left}
    (H : LBIso L' (L.pull φ)) {a' b' : T' ⟶ G'} {a b : T ⟶ G} (ha : pushPt h.1.w a' = U ≫ a)
    (hb : pushPt h.1.w b' = U ≫ b) : LBIso (cubeLB G' ![a', b'] L') ((cubeLB G ![a, b] L).pull U.left) :=
  iso_linComb_pull H _ _ _ U.left fun I => psum_push h _ _ U (fun i => by
    fin_cases i
    exacts [ha, hb]) I.down

end Points

def sqMap : Over.mk ((G' ⊗ G').hom ≫ f) ⟶ G ⊗ G := lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G'))

theorem push_fst : pushPt h.1.w (fst G' G') = sqMap h ≫ fst G G := (lift_fst _ _).symm

theorem push_snd : pushPt h.1.w (snd G' G') = sqMap h ≫ snd G G := (lift_snd _ _).symm

theorem isPullback_sqMap : IsPullback (sqMap h).left (G' ⊗ G').hom (G ⊗ G).hom f := by
  have e₁ : (sqMap h).left ≫ (fst G G).left = (fst G' G').left ≫ φ := congrArg (fun q => q.left) (push_fst h).symm
  have e₂ : (sqMap h).left ≫ (snd G G).left = (snd G' G').left ≫ φ := congrArg (fun q => q.left) (push_snd h).symm
  have A : IsPullback (snd G G).left (fst G G).left G.hom G.hom := (IsPullback.of_hasPullback G.hom G.hom).flip
  have A' : IsPullback (snd G' G').left (fst G' G').left G'.hom G'.hom := (IsPullback.of_hasPullback G'.hom G'.hom).flip
  have B := A'.paste_horiz h.1
  rw [← e₂, ← h.1.w] at B
  have C := (IsPullback.of_right B e₁ A).paste_vert h.1
  rwa [Over.w, Over.w] at C

def selfMap : Over.mk (G'.hom ≫ f) ⟶ G := Over.homMk φ h.1.w

theorem push_id : pushPt h.1.w (𝟙 G') = selfMap h ≫ 𝟙 G :=
  Over.OverMorphism.ext ((Category.id_comp _).trans (Category.comp_id _).symm)

theorem push_end {a' : G' ⟶ G'} {a : G ⟶ G} (ha : a'.left ≫ φ = φ ≫ a.left) : pushPt h.1.w a' = selfMap h ≫ a :=
  Over.OverMorphism.ext ha

end Group

variable {o : Type} [CommRing o] {g k : ℕ} {J : Type} {b : TBase o k}

theorem isLB_linComb {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] (ψ : K → (Y ⟶ X))
    (ε : K → ℤ) : (LB.LinComb L ψ ε).IsLB := DVR.linComb_isLB _ hL _ _

theorem transfer {K : Type} [Field K] {S₁ S₂ : Scheme.{0}} [Nonempty S₁] {s₀ : Sp K ⟶ Sp o} {s₁ : S₁ ⟶ Sp o}
    {s₂ : S₂ ⟶ Sp o} {f₁ : S₁ ⟶ Sp K} {f₂ : S₂ ⟶ Sp K} {t₀ : TObj g k J b s₀} {t₁ : TObj g k J b s₁}
    {t₂ : TObj g k J b s₂} (H₁ : TMap t₁ t₀ f₁) (H₂ : TMap t₂ t₀ f₂) (w w' : J) :
    (LBIso (cubeLB t₁.A ![fst t₁.A t₁.A ≫ t₁.act w, snd t₁.A t₁.A] t₁.L)
        (cubeLB t₁.A ![fst t₁.A t₁.A, snd t₁.A t₁.A ≫ t₁.act w'] t₁.L) →
      LBIso (cubeLB t₂.A ![fst t₂.A t₂.A ≫ t₂.act w, snd t₂.A t₂.A] t₂.L)
        (cubeLB t₂.A ![fst t₂.A t₂.A, snd t₂.A t₂.A ≫ t₂.act w'] t₂.L)) ∧
    (LBIso t₁.L (cubeLB t₁.A ![𝟙 t₁.A, t₁.act w] t₁.L) → LBIso t₂.L (cubeLB t₂.A ![𝟙 t₂.A, t₂.act w] t₂.L)) := by
  obtain ⟨φ, h, hL, -, hact⟩ := H₁
  obtain ⟨φ', h', hL', -, hact'⟩ := H₂
  let _ := t₀.ab.comm
  let _ := t₁.ab.comm
  let _ := t₂.ab.comm
  have := t₀.ab.smooth
  have := t₀.ab.proper
  have := t₀.ab.geomConnected
  have pr : IsProper (t₀.A ⊗ t₀.A).hom := by
    rw [Over.tensorObj_hom]
    infer_instance
  have i₂ := iso_cubeLB_pull h _ hL (push_comp h _ (push_fst h) (hact w)) (push_snd h)
  have i₃ := iso_cubeLB_pull h _ hL (push_fst h) (push_comp h _ (push_snd h) (hact w'))
  have i₄ := iso_cubeLB_pull h _ hL (push_id h) (push_end h (hact w))
  have j₂ := iso_cubeLB_pull h' _ hL' (push_comp h' _ (push_fst h') (hact' w)) (push_snd h')
  have j₃ := iso_cubeLB_pull h' _ hL' (push_fst h') (push_comp h' _ (push_snd h') (hact' w'))
  have j₄ := iso_cubeLB_pull h' _ hL' (push_id h') (push_end h' (hact' w))
  refine ⟨fun H => ?_, fun H => ?_⟩
  · have d := iso_down (isPullback_sqMap h) (smooth_tensorObj_hom _ _) pr (geometricallyConnected_tensorObj_hom _ _)
      (isLB_linComb t₀.isLB _ _) (isLB_linComb t₀.isLB _ _) (isLB_linComb t₁.isLB _ _) (isLB_linComb t₁.isLB _ _)
      i₂ i₃ H
    exact iso_up (isLB_linComb t₀.isLB _ _) (isLB_linComb t₀.isLB _ _) (isLB_linComb t₂.isLB _ _)
      (isLB_linComb t₂.isLB _ _) j₂ j₃ d
  · have d := iso_down h.1 ‹_› ‹_› ‹_› t₀.isLB (isLB_linComb t₀.isLB _ _) t₁.isLB (isLB_linComb t₁.isLB _ _) hL i₄ H
    exact iso_up t₀.isLB (isLB_linComb t₀.isLB _ _) t₂.isLB (isLB_linComb t₂.isLB _ _) hL' j₄ d

theorem adjoint_primitive_of_dense : Out.GlobalFnsSt → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (h g : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (J : Type) (a : J → Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))) (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (em : o →+* ℂ) (S : Scheme.{0}) [IsReduced S] (s : S ⟶ Sp o) (t : TObj g k J b s), Dense (fromSet em (SharpClass (b := b) W a bas em) t) → (∀ j j', (a j).transpose * (W + W.transpose) = (W + W.transpose) * a j' → LBIso (cubeLB t.A ![fst t.A t.A ≫ t.act j, snd t.A t.A] t.L) (cubeLB t.A ![fst t.A t.A, snd t.A t.A ≫ t.act j'] t.L)) ∧ ∀ j, (W + W.transpose) * a j = W → LBIso t.L (cubeLB t.A ![𝟙 t.A, t.act j] t.L) := by
  intro hG cube h g W J a bas k o _ b em S _ s t hd
  let _ := t.ab.comm
  have : Nonempty (Sp ℂ) := inferInstanceAs (Nonempty (PrimeSpectrum ℂ))
  refine ⟨fun j j' hj => GlobalTheory.T.adjoint_endomorphisms_cubeLB_of_dense_fibres hG S t.A t.L _ _ t.ab t.isLB t.ample (t.hom j) (t.hom j') (hd.mono ?_),
    fun j hj => GlobalTheory.T.lbIso_cube_graph_of_dense_fibres hG S t.A t.L _ t.ab t.isLB t.ample t.rigid (t.hom j) (hd.mono ?_)⟩
  · rintro p ⟨K, _, x, hp, K₀, _, β, i, i', t₀, tx, tc, -, -, ⟨φ, hφ, hL, -, hact⟩, m₂, m₁, c, -, pr, hm, hu, hl,
      hmat, -⟩
    exact ⟨K, inferInstance, x, tx.A, inferInstance, tx.ab.comm, φ, tx.L, tx.act j, tx.act j', hp, hφ, tx.isLB, hL,
      hact j, hact j', (transfer m₁ m₂ j j').1 ((PowerAdjoint.matrix_primitive_adjoint cube W ℂ o _ h k _ c tc.pol pr
        hm hu hl (a j) (tc.act j) (hmat j)).2 (a j') (tc.act j') (hmat j') hj)⟩
  · rintro p ⟨K, _, x, hp, K₀, _, β, i, i', t₀, tx, tc, -, -, ⟨φ, hφ, hL, -, hact⟩, m₂, m₁, c, -, pr, hm, hu, hl,
      hmat, -⟩
    exact ⟨K, inferInstance, x, tx.A, inferInstance, tx.ab.comm, φ, tx.L, tx.act j, hp, hφ, tx.isLB, hL,
      hact j, (transfer m₁ m₂ j j).2 ((PowerAdjoint.matrix_primitive_adjoint cube W ℂ o _ h k _ c tc.pol pr
        hm hu hl (a j) (tc.act j) (hmat j)).1 hj)⟩

end GlobalTheory.SharpAdjoint
