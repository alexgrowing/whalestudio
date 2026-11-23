import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemberStepCharts
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemberLevelPrimeNotMemUnderLevelPrimes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalGroupElementEqLevelComponentBadPrime
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceProjectionEqOfPrimeComponentEqStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdAtToEAfOfIsIdemSum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam.MovedJoin
open GlobalTheory.AdForm

open Formalism.L2.Col in

theorem adAt_kb_eq_frsF {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι}
    {Ch₀ : ℕ → Type} (A : TwDat I l Z u a Ch₀) (hA : A.Is) (P : BadPr I a) (hP : P.1 ∉ (B.primes X).vGs)
    (i : ℕ) (hi : i ≤ B.R.m) (β : Ch₀ i) (r s : Fin (B.R.N i)) :
    adAt B.host.F P.1 (((A.kb i β : TC.GA B (B.R.N i)) : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) _) r s) =
      algebraMap B.host.E _ (frsF I.sel (I.tup a) (A.p0 i β).1.1 P (Pi.single s 1) r) := by
  have hQ : P.1 ∈ I.Q a := by
    rcases Finset.mem_union.1 P.2 with h | h
    · exact absurd h hP
    · exact h
  have hSQ : P.1 ∈ I.SQ := Finset.mem_biUnion.2 ⟨a, Finset.mem_univ _, hQ⟩
  have h1 := ((hA.base i hi β).1).fr ⟨P.1, hSQ⟩ r s
  rw [h1, extTo_fr, frsF_eq_ptFr]

theorem adAt_kStd_of_twist {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} (hI : I.Ok) (a : I.ι) (P : BadPr I a)
    (hP : P.1 ∉ (B.primes X).vGs) (u : B.Word) (n : ℕ) (r s : Fin n) :
    adAt B.host.F P.1 (((TC.kStd X u n : TC.GA B n) : Matrix (Fin n) (Fin n) _) r s) =
      algebraMap B.host.E _ (if r = s then 1 else 0) := by
  have hQ : P.1 ∈ I.Q a := by
    rcases Finset.mem_union.1 P.2 with h | h
    · exact absurd h hP
    · exact h
  have hSQ : P.1 ∈ I.SQ := Finset.mem_biUnion.2 ⟨a, Finset.mem_univ _, hQ⟩
  have hT := GlobalTheory.Mem.LevTwist.T_notMem_under_uSG B X I hI u P.1 (Finset.mem_union_right _ hSQ)
  have hb := (GlobalTheory.Mem.Col2.MemChart.kStd_spec (X := X) (GlobalTheory.BasePrimes.primes_ok B X).1 u n).2.1 _ hT
  have he := congrArg (fun g => (g.1 : Matrix (Fin n) (Fin n) _) r s) hb
  simp only [Units.val_one] at he
  have h2 : Formalism.UG.prV (E := B.host.E) (P.1.under (𝓞 B.host.F)) (((TC.kStd X u n : TC.GA B n) : Matrix (Fin n) (Fin n) _) r s) =
      Formalism.UG.prV (E := B.host.E) (P.1.under (𝓞 B.host.F)) ((1 : Matrix (Fin n) (Fin n) (AfE B.host.F B.host.E)) r s) := by
    refine he.trans ?_
    by_cases h : r = s <;> simp [Matrix.one_apply, h]
  rw [GlobalTheory.Mem.Col2.AdT.LocSplice.adAt_eq_of_prV P.1 h2]
  by_cases h : r = s <;> simp [Matrix.one_apply, h]

theorem map_eq_one_of_pr {D : Formalism.BasicNotions.D7} {k : Type} [CommRing k] {n : ℕ} (φ : Formalism.L2.Theta.AE D →+* k)
    (M : Matrix (Fin n) (Fin n) (Formalism.L2.Theta.AE D))
    (h : ∀ c d, φ (M c d) = φ (Formalism.L2.Theta.incA D (if c = d then 1 else 0))) : M.map φ = 1 := by
  ext c d
  rw [Matrix.map_apply, h, Matrix.one_apply]
  split_ifs <;> simp

theorem mul_frameγ_std {k : Type} [Field k] {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y] (F : Frame k N Y) (e' : Y ≃ Fin N)
    (hF : F.β = (1 : Matrix (Fin N) (Fin N) k).submatrix id e') (M : Matrix (Fin N) Y k) (r : Fin N) (b : Y) :
    (M * F.γ) r (e' b) = M r b := by
  have h1 : M * F.γ * F.β = M := by rw [Matrix.mul_assoc, F.γβ, Matrix.mul_one]
  have h2 := congrFun (congrFun h1 r) b
  rw [hF, Matrix.mul_apply] at h2
  simp only [Matrix.submatrix_apply, id, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h2
  exact h2

theorem frameβ_mul_std {k : Type} [Field k] {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y] (F : Frame k N Y) (e' : Y ≃ Fin N)
    (hF : F.β = (1 : Matrix (Fin N) (Fin N) k).submatrix id e') (g : Matrix Y Y k) (r b : Y) :
    (F.β * g) (e' r) b = g r b := by
  rw [hF, Matrix.mul_apply]
  simp only [Matrix.submatrix_apply, id, Matrix.one_apply, EmbeddingLike.apply_eq_iff_eq, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem map_eq_sum_frame {E k : Type} [Field E] [CommRing k] {n : ℕ} (φ : E →+* k) (f : (Fin n → E) ≃ₗ[E] (Fin n → E)) (y : Fin n → E)
    (x : Fin n) : φ (y x) = ∑ c, φ (f (Pi.single c 1) x) * φ (f.symm y c) := by
  conv_lhs => rw [← f.apply_symm_apply y, pi_eq_sum_univ' (f.symm y), map_sum]
  rw [Finset.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul, map_mul, mul_comm]

end GlobalTheory.Fam.MovedJoin

namespace GlobalTheory.Fam
open GlobalTheory.AdForm GlobalTheory.Fam.MovedJoin

set_option maxHeartbeats 1000000 in

theorem QJ.Reads.movedAt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → ∀ t (J : QJ a t), J.Reads → ∀ i, MovedAt J.A (J.P i) (J.E i) (J.hψ i) (J.sg i) (J.π i) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha t J hJ i
  refine { toReadsAt := ⟨hJ.eq i, hJ.tw i, hJ.M i, hJ.rep i⟩, rk := fun _ => rfl, low := ?_, pen := ?_ }
  · intro k hk hm β e he r b
    have hs : (a.Q (J.pl i) ⟨t, J.mem i⟩).s + 1 + 1 = B.R.m := (a.Q (J.pl i) ⟨t, J.mem i⟩).hs
    have hstd := hJ.std k (by omega) β
    have hPn : (J.P i).1 ∉ (B.primes X).vGs := (hJ.tw i).nmem
    obtain ⟨e', he', hF⟩ := (ha.stdQ (J.pl i) ⟨t, J.mem i⟩).1 k (Nat.le_succ_of_le hk)
    rw [hF]
    have key : ∀ r' b' : Fin (B.R.N k), Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 k β).1.1 (J.P i) (Pi.single b' 1) r' =
        if r' = b' then (1 : B.host.E) else 0 := by
      intro r' b'
      apply (algebraMap B.host.E ((J.P i).1.adicCompletion B.host.E)).injective
      rw [← adAt_kb_eq_frsF J.A hJ.is (J.P i) hPn k hm β r' b', hstd, adAt_kStd_of_twist hW.tr.ok _ (J.P i) hPn u _ r' b']
    unfold baseFr
    refine (congrArg _ (key _ _)).trans ?_
    have hiff : ((finCongr (rankN (I.rec7 l Z) k hm)) (Fin.cast rfl r) = e b) ↔ (r = e' b) := by
      constructor
      · intro h
        exact Fin.ext ((congrArg Fin.val h).trans ((he b).trans (he' b).symm))
      · intro h
        exact Fin.ext ((congrArg Fin.val h).trans ((he' b).trans (he b).symm))
    have hR : ∀ x : (a.Q (J.pl i) ⟨t, J.mem i⟩).k, x = (if r = e' b then 1 else 0) →
        x = Matrix.submatrix (1 : Matrix (Fin ((commOf (pk W) u a.g).X k).rank) (Fin ((commOf (pk W) u a.g).X k).rank) (a.Q (J.pl i) ⟨t, J.mem i⟩).k) id e' r b := by
      intro x hx
      rw [hx]
      rfl
    apply hR
    split_ifs with h1 h2 h2
    · simp only [GlobalTheory.LocMod.Place.pr]
      exact (congrArg _ (map_one _)).trans (map_one _)
    · exact absurd (hiff.1 h1) h2
    · exact absurd (hiff.2 h2) h1
    · simp only [GlobalTheory.LocMod.Place.pr]
      exact (congrArg _ (map_zero _)).trans (map_zero _)
  · intro hm β e he
    have hs : (J.G i).s + 1 + 1 = B.R.m := (J.G i).hs
    have hPn : (J.P i).1 ∉ (B.primes X).vGs := (hJ.tw i).nmem
    have hidem : Formalism.L2.NTheta.IsIdemAt (J.G i).q.e (J.P i).1 := by rw [hJ.eq i]; exact (J.G i).idem
    obtain ⟨k₀, h, hk₀, hfin, hkA, hh, hg⟩ := hJ.pen ((J.G i).s + 1) (by omega) β
    obtain ⟨g, hgJ, hgm⟩ := hg i rfl
    obtain ⟨e', he', hF⟩ := (ha.stdQ (J.pl i) ⟨t, J.mem i⟩).1 ((J.G i).s + 1) le_rfl
    have hkb := (hJ.is.kA ((J.G i).s + 1) hm β).2.1
    have hent : ∀ (y : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X ((J.G i).s + 1))) (c d : Fin ((I.rec7 l Z).sp.X ((J.G i).s + 1)).rank),
        finM _ (rankN (I.rec7 l Z) ((J.G i).s + 1) hm) y (finCongr (rankN (I.rec7 l Z) ((J.G i).s + 1) hm) c)
          (finCongr (rankN (I.rec7 l Z) ((J.G i).s + 1) hm) d) = toEAf (I.rec7 l Z) (Formalism.L2.Theta.mt _ y c d) := by
      intro y c d
      simp [finM, Matrix.reindex_apply]
    have hent' : ∀ (y : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X ((J.G i).s + 1))) (c d : Fin (B.R.N ((J.G i).s + 1))),
        finM _ (rankN (I.rec7 l Z) ((J.G i).s + 1) hm) y c d = toEAf (I.rec7 l Z) (Formalism.L2.Theta.mt _ y
          ((finCongr (rankN (I.rec7 l Z) ((J.G i).s + 1) hm)).symm c) ((finCongr (rankN (I.rec7 l Z) ((J.G i).s + 1) hm)).symm d)) := by
      intro y c d
      rfl
    have hk0 : (Formalism.L2.Theta.mt _ k₀).map (J.G i).q.pr = 1 := by
      refine map_eq_one_of_pr _ _ fun c d => GlobalTheory.T.splitPlaceProjection_eq_of_primeComponent_eq _ _ hidem _ _ ?_
      have h1 := congrFun (congrFun hfin (finCongr (rankN (I.rec7 l Z) ((J.G i).s + 1) hm) c))
        (finCongr (rankN (I.rec7 l Z) ((J.G i).s + 1) hm) d)
      rw [hent] at h1
      refine (congrArg (adAt B.host.F (J.P i).1) h1).trans ((adAt_kStd_of_twist hW.tr.ok _ (J.P i) hPn u _ _ _).trans ?_)
      have hite : (if finCongr (rankN (I.rec7 l Z) ((J.G i).s + 1) hm) c = finCongr (rankN (I.rec7 l Z) ((J.G i).s + 1) hm) d
          then (1 : B.host.E) else 0) = if c = d then 1 else 0 := by
        by_cases hcd : c = d
        · subst hcd
          simp
        · rw [if_neg (fun h' => hcd ((finCongr _).injective h')), if_neg hcd]
      exact congrArg _ hite
    have hkAm : (Formalism.L2.Theta.mt _ (J.A.kA ((J.G i).s + 1) β)).map (J.G i).q.pr =
        ((J.G i).FX ((J.G i).s + 1) le_rfl).β * g.val.toBlocks₁₁ * ((J.G i).FX ((J.G i).s + 1) le_rfl).γ := by
      rw [hkA, GlobalTheory.AdForm.CongAtIdem.mt_mul', Matrix.map_mul, hk0, Matrix.one_mul]
      exact hgm
    have hentry : ∀ (x : Fin (B.R.N ((J.G i).s + 1))) (b : StepData.XIx (Fin B.R.k) (Fin B.R.t) ((J.G i).s + 1)),
        (ofSplit (J.G i).q).pr (Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 ((J.G i).s + 1) β).1.1 (J.P i) (Pi.single (e b) 1) x) =
          (((J.G i).FX ((J.G i).s + 1) le_rfl).β * g.val.toBlocks₁₁) ((finCongr (rankN (I.rec7 l Z) ((J.G i).s + 1) hm)).symm x) b := by
      intro x b
      have h1 := adAt_kb_eq_frsF J.A hJ.is (J.P i) hPn _ hm β x (e b)
      rw [← hkb] at h1
      have h2 : adAt B.host.F (J.P i).1 (toEAf (I.rec7 l Z) (Formalism.L2.Theta.mt _ (J.A.kA ((J.G i).s + 1) β)
          ((finCongr (rankN (I.rec7 l Z) ((J.G i).s + 1) hm)).symm x) ((finCongr (rankN (I.rec7 l Z) ((J.G i).s + 1) hm)).symm (e b)))) =
          algebraMap B.host.E _ (Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 ((J.G i).s + 1) β).1.1 (J.P i) (Pi.single (e b) 1) x) := by
        have h5 := hent' (J.A.kA ((J.G i).s + 1) β) x (e b)
        exact (congrArg (adAt B.host.F (J.P i).1) h5).symm.trans h1
      have h3 := GlobalTheory.T.splitPlaceProjection_eq_of_primeComponent_eq _ _ hidem _ _ h2
      have h4 : (finCongr (rankN (I.rec7 l Z) ((J.G i).s + 1) hm)).symm (e b) = e' b := Fin.ext ((he b).trans (he' b).symm)
      refine h3.symm.trans ?_
      refine (congrArg (fun c => (J.G i).q.pr (Formalism.L2.Theta.mt _ (J.A.kA ((J.G i).s + 1) β)
          ((finCongr (rankN (I.rec7 l Z) ((J.G i).s + 1) hm)).symm x) c)) h4).trans ?_
      refine (congrFun (congrFun hkAm _) (e' b)).trans ?_
      exact mul_frameγ_std _ e' hF _ _ _
    refine ⟨g, hgJ, fun r b => hentry _ b, ?_⟩
    refine (hJ.cos i β e he).trans (congrArg _ ?_)
    funext r
    have hexp := map_eq_sum_frame ((J.G i).q.pr.comp (incA (I.rec7 l Z)))
      (Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 ((J.G i).s + 1) β).1.1 (J.P i))
      (Formalism.L2.Col.repY (J.A.p0 ((J.G i).s + 1) β).1.2) (e r)
    refine hexp.trans ?_
    refine (Equiv.sum_comp e (fun c => ((J.G i).q.pr.comp (incA (I.rec7 l Z)))
      (Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 ((J.G i).s + 1) β).1.1 (J.P i) (Pi.single c 1) (e r)) *
      ((J.G i).q.pr.comp (incA (I.rec7 l Z))) ((Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 ((J.G i).s + 1) β).1.1 (J.P i)).symm
        (Formalism.L2.Col.repY (J.A.p0 ((J.G i).s + 1) β).1.2) c))).symm.trans ?_
    refine Finset.sum_congr rfl fun b _ => ?_
    have h4 : (finCongr (rankN (I.rec7 l Z) ((J.G i).s + 1) hm)).symm (e r) = e' r := Fin.ext ((he r).trans (he' r).symm)
    have H := (hentry (e r) b).trans ((congrArg (fun c => (((J.G i).FX ((J.G i).s + 1) le_rfl).β * g.val.toBlocks₁₁) c b) h4).trans
      (frameβ_mul_std _ e' hF _ r b))
    exact congrArg₂ (· * ·) H rfl

end GlobalTheory.Fam
