import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.KerIsTerm
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelChainSharpColumnValuationOfPointKernelLiftL
import Formalism.LocalToGlobal.Columns.PolyFnLemmas

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built

noncomputable section
namespace GlobalTheory.LvT.Built.DilPass

variable {D : D7} {u : D.what₂.Word}

theorem isAct_unique {q : ℕ} {F : Type} [Field F] {Lc : LocF q F} {n : ℕ} {g : GL (Fin n) Lc.K} {p p₁ p₂ : LocF.PP Lc n}
    (h₁ : p.IsAct g p₁) (h₂ : p.IsAct g p₂) : p₁ = p₂ := by
  have hs : ∀ x : Fin n → Lc.K, ∃ y, Matrix.mulVec (g : Matrix (Fin n) (Fin n) Lc.K) y = x := fun x =>
    ⟨Matrix.mulVec ((g⁻¹ : GL (Fin n) Lc.K) : Matrix (Fin n) (Fin n) Lc.K) x, by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]⟩
  apply Subtype.ext
  apply LocF.Raw.ext
  · ext x
    obtain ⟨y, rfl⟩ := hs x
    rw [(h₁ y).1, (h₂ y).1]
  · funext x
    obtain ⟨y, rfl⟩ := hs x
    rw [(h₁ y).2, (h₂ y).2]

theorem isDil_act {q : ℕ} {F : Type} [Field F] {Lc : LocF q F} {n : ℕ} {g : GL (Fin n) Lc.K} {a : F}
    {p p' p₁ p₁' : LocF.PP Lc n} (h : LocF.PP.IsDil a p p') (h₁ : p.IsAct g p₁) (h₂ : p'.IsAct g p₁') :
    LocF.PP.IsDil a p₁ p₁' := by
  have hs : ∀ x : Fin n → Lc.K, ∃ y, Matrix.mulVec (g : Matrix (Fin n) (Fin n) Lc.K) y = x := fun x =>
    ⟨Matrix.mulVec ((g⁻¹ : GL (Fin n) Lc.K) : Matrix (Fin n) (Fin n) Lc.K) x, by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]⟩
  refine ⟨?_, fun x => ?_⟩
  · ext x
    obtain ⟨y, rfl⟩ := hs x
    rw [(h₁ y).1, (h₂ y).1, h.1]
  · obtain ⟨y, rfl⟩ := hs x
    rw [(h₁ y).2, (h₂ y).2, h.2]

theorem dil_smul {X : Ch D u} {i : ℕ} (M : PtModel X i) {v : X.A.vT} {a : X.A.Fv v} {p q : M.Pt} (h : M.Dil v a p q)
    (g : M.G) : M.Dil v a (g • p) (g • q) := by
  refine ⟨M.smul_fst g q p h.1, fun v' hv => ?_, isDil_act h.2.2 (M.smul_snd g p v) (M.smul_snd g q v)⟩
  have h1 := M.smul_snd g q v'
  rw [h.2.1 v' hv] at h1
  exact isAct_unique h1 (M.smul_snd g p v')

theorem dil_unique {X : Ch D u} {i : ℕ} (M : PtModel X i) {v : X.A.vT} {a : X.A.Fv v} {p q q' : M.Pt} (h : M.Dil v a p q)
    (h' : M.Dil v a p q') : q = q' := by
  refine Prod.ext (h.1.trans h'.1.symm) (funext fun v' => ?_)
  by_cases hv : v' = v
  · subst hv
    apply Subtype.ext
    apply LocF.Raw.ext
    · rw [h.2.2.1, h'.2.2.1]
    · funext x
      rw [h.2.2.2, h'.2.2.2]
  · rw [h.2.1 v' hv, h'.2.1 v' hv]

theorem dil_pt {B : Built.Dat D u} {i : ℕ} {sp : Split (B.J.A i) B.J.T} {M : PtModel B.ch i} (R : B.Real i sp M)
    (v : B.ch.A.vT) (a : (B.ch.A.Fv v)ˣ) (b : (B.I.S i).β) (d : (B.I.S i).D b) :
    M.Dil v a (R.pt b d) (R.pt b ((B.J.A i).dia b (B.pr v) a d)) := by
  have hs : ∀ (P : B.ch.A.vT) (x : Fin (D.R.N i) → (M.Lc P).K), ∃ y : Fin (D.R.N i) → B.E, (fun c => R.iK P (y c)) = x :=
    fun P x => ⟨fun c => (R.iK P).symm (x c), funext fun c => by simp⟩
  have hL : ∀ P, ((R.pt b ((B.J.A i).dia b (B.pr v) a d)).2 P).1.L = ((R.pt b d).2 P).1.L := by
    intro P
    ext x
    obtain ⟨y, rfl⟩ := hs P x
    rw [R.pt_L, R.pt_L, (B.hJ.lev i).dia_N b (B.pr v) a d]
  refine ⟨?_, fun v' hv => ?_, hL v, fun x => ?_⟩
  · have h := (R.fst 1 b ((B.J.A i).dia b (B.pr v) a d) d).2
      ⟨1, map_one _, map_one _, by rw [one_smul]; exact (sp.off b).symm (sp.off_dia b d (B.pr v) a)⟩
    rwa [map_one, one_smul] at h
  · apply Subtype.ext
    apply LocF.Raw.ext (hL v')
    funext x
    obtain ⟨y, rfl⟩ := hs v' x
    exact (R.pt_f _ _ v' y).trans ((congrFun (sp.dia_deco b d (B.pr v) (B.pr v') a hv) y).trans (R.pt_f _ _ v' y).symm)
  · obtain ⟨y, rfl⟩ := hs v x
    refine (R.pt_f _ _ v y).trans (((B.hJ.lev i).dia_f b (B.pr v) a d y).trans ?_)
    rw [← R.pt_f b d v y]
    rfl

theorem ext_ev {B : Built.Dat D u} {i : ℕ} {sp : Split (B.J.A i) B.J.T} {M : PtModel B.ch i} (R : B.Real i sp M)
    {V : Type} [AddCommGroup V] [Module ℂ V] (φ ψ : M.Val →ₗ[ℂ] V)
    (h : ∀ F (y : M.Val), y.1 = B.ev i F → φ y = ψ y) : φ = ψ := by
  have hsp : M.Val = Submodule.span ℂ (Set.range (B.ev i)) := R.val_eq.trans (span_evV _ _ _ _).symm
  ext ⟨y, hy⟩
  have hy' : y ∈ Submodule.span ℂ (Set.range (B.ev i)) := hsp ▸ hy
  have key : ∀ y ∈ Submodule.span ℂ (Set.range (B.ev i)), ∀ hy : y ∈ M.Val, φ ⟨y, hy⟩ = ψ ⟨y, hy⟩ := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨F, rfl⟩ := hz
      exact fun hy => h F _ rfl
    | zero => exact fun hy => (map_zero φ).trans (map_zero ψ).symm
    | add a b ha hb iha ihb =>
      intro hy
      have ha' : a ∈ M.Val := hsp ▸ ha
      have hb' : b ∈ M.Val := hsp ▸ hb
      exact (map_add φ ⟨a, ha'⟩ ⟨b, hb'⟩).trans ((congrArg₂ (· + ·) (iha ha') (ihb hb')).trans (map_add ψ ⟨a, ha'⟩ ⟨b, hb'⟩).symm)
    | smul r a ha iha =>
      intro hy
      have ha' : a ∈ M.Val := hsp ▸ ha
      exact (map_smul φ r ⟨a, ha'⟩).trans ((congrArg (r • ·) (iha ha')).trans (map_smul ψ r ⟨a, ha'⟩).symm)
  exact key y hy' hy

theorem dilLaw_of_kerDil : ∀ (D : D7) (u : D.what₂.Word) (B : Built.Dat D u) (i : ℕ) (sp : Split (B.J.A i) B.J.T) (sp' : Split (B.J.A (i + 1)) B.J.T) (M : PtModel B.ch i) (M' : PtModel B.ch (i + 1)) (R : B.Real i sp M) (R' : B.Real (i + 1) sp' M') (k : B.Ker i) (K : KerPt M M'), K.TgtEq → Built.Dat.KerIs R R' K k → Built.Dat.KerDil k → K.DilLaw := by
  intro D u B i sp sp' M M' R R' k K hT hI hD v a p q p' q' h h'
  obtain ⟨ζ, b, d, rfl⟩ := R.surj p
  obtain ⟨ζ', b', d', rfl⟩ := R'.surj p'
  have hq := dil_unique M h (dil_smul M (dil_pt R v a b d) (R.zeta ζ))
  have hq' := dil_unique M' h' (dil_smul M' (dil_pt R' v a b' d') (R'.zeta ζ'))
  have h0 : K.k (R.pt b ((B.J.A i).dia b (B.pr v) a d)) (R'.pt b' ((B.J.A (i + 1)).dia b' (B.pr v) a d')) =
      K.k (R.pt b d) (R'.pt b' d') := by
    refine ext_ev R _ _ fun F y hy => Subtype.ext ?_
    rw [hI _ _ _ _ F y hy, hI _ _ _ _ F y hy, hD b b' d d' (B.pr v) a]
  have hs : ∀ y : M.Val, M.act (R.zeta ζ) (M.act (R.zeta ζ)⁻¹ y) = y := fun y => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  rw [hq, hq']
  refine LinearMap.ext fun y => ?_
  rw [← hs y, K.src, K.src, hT, hT, h0]

end GlobalTheory.LvT.Built.DilPass
