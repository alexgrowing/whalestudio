import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.DatDatum
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ExCusp
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.SInfEx
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.SInfIff
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.SSatIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalSatakeAlmostAll
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseChangeSpehOfDiscreteSeries

open NumberField MeasureTheory GlobalTheory.CuspRep GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.V UpperTheory.ConvolutionTheory.C

namespace UpperTheory.ConvolutionTheory.BW.BlockSaturationData

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {S : Set (Pl E)}

private theorem blo_at {r : ℕ} (b : Blo S r) : ∃ V, IsSummand (mu1 E r) V ∧
    At (mu1 E r) S V (fun τ => Finset.univ.val.map (b.Λ τ)) fun w => (b.sat w).map fun x : ℂˣ => (x : ℂ) := by
  obtain ⟨V, hV, hf⟩ := b.summand
  obtain ⟨π, hπ, -⟩ := Dp.exCusp E r (mu1 E r) V hV
  have hc : (⟨b.f.1, b.cusp⟩ : AutomorphicForm.cuspForms E r) ∈ AutomorphicForm.centralCuspForms E r := fun s x => by
    have := b.cen (Real.log s.1) x
    unfold zt at this
    simpa only [Real.exp_log s.2] using this
  have hm : b.f ∈ π.V := by
    have : (⟨b.f.1, b.cusp⟩ : AutomorphicForm.cuspForms E r) ∈ Cm.carrier π := by
      rw [hπ.carrier_eq]; exact ⟨hc, hf⟩
    exact this
  refine ⟨V, hV, fun τ => ?_, fun w hw => ?_⟩
  · obtain ⟨m, h1, -⟩ := Dp.sInfEx E r (mu1 E r) V hV τ
    have h2 : GlobalTheory.UnitaryBC.HasInfCharGL π.V τ m := (Dp.sInfIff E r (mu1 E r) π V hπ τ m).1 h1
    have hs : Submodule.span ℂ {b.f} ≠ ⊥ := by simpa using b.ne
    have e : m = Finset.univ.val.map (b.Λ τ) := by
      refine GlobalTheory.BcSpehProof.hasInfCharGL_unique hs (τ := τ) ⟨h2.1, fun u φ hφ => h2.2 u φ ?_⟩ ⟨by simp, fun u φ hφ => ?_⟩
      · exact Submodule.span_le.2 (Set.singleton_subset_iff.2 hm) hφ
      · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hφ
        rw [map_smul, b.inf, smul_comm, Multiset.map_map]
        rfl
    rw [e] at h1
    exact h1
  · have h0 := b.isSat w hw
    have hx : (⟨b.f, hm⟩ : π.V) ∈ GlobalTheory.PRep.fixed (π.locRep w) (GlobalTheory.LFun.KGL w r) :=
      GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext (GlobalTheory.LGrp.mem_fixed.1 h0.2.1 k hk)
    have hne : (⟨b.f, hm⟩ : π.V) ≠ 0 := fun e => b.ne (congrArg Subtype.val e)
    obtain ⟨B, hB⟩ := GlobalTheory.CompanionTheory.SatAe.exists_hasSatGL_locRep π w ((Submodule.ne_bot_iff _).2 ⟨_, hx, hne⟩)
    have h1 : GlobalTheory.LFun.IsSatVecGL w (rw r w) b.f B := (hB.2 _ hx hne).map π.V.subtype (fun _ _ => rfl) b.ne
    have e := h1.unique h0
    subst e
    exact (Dp.sSatIff E r (mu1 E r) π V hπ w _).2 ⟨_, rfl, hB⟩

private def blk : {n : ℕ} → (d : Dat S n) → Fin d.len → Σ r, Blo S r
  | _, .nil => fun j => j.elim0
  | _, .cons b d => fun j => Fin.cases (motive := fun _ => Σ r, Blo S r) ⟨_, b⟩ (blk d) (j : Fin (d.len + 1))

private theorem blk_sum : ∀ {n : ℕ} (d : Dat S n), ∑ j, (blk d j).1 = n
  | _, .nil => rfl
  | _, .cons b d => by
    have := blk_sum d
    exact (Fin.sum_univ_succ (n := d.len) _).trans (congrArg (_ + ·) this)

private theorem blk_sat : ∀ {n : ℕ} (d : Dat S n) (j : Fin d.len), d.sat j = (blk d j).2.sat
  | _, .nil, j => j.elim0
  | _, .cons b d, j => by
    refine Fin.cases (motive := fun j : Fin (d.len + 1) => (Dat.cons b d).sat j = (blk (.cons b d) j).2.sat) rfl
      (fun i => blk_sat d i) j

private theorem map_addCases {r s : ℕ} (f : Fin (r + s) → ℂ) :
    Finset.univ.val.map f = (Finset.univ.val.map fun i => f (Fin.castAdd s i)) + Finset.univ.val.map fun i => f (Fin.natAdd r i) := by
  simp only [Fin.univ_val_map, List.ofFn_add, Multiset.coe_add]
  rfl

private theorem blk_ms (τ : E →+* ℂ) : ∀ {n : ℕ} (d : Dat S n) (z : Fin d.len → ℂ),
    msOf (d.ptL z) τ = ∑ j, (Finset.univ.val.map ((blk d j).2.Λ τ)).map (· + z j)
  | _, .nil, _ => rfl
  | _, .cons b d, z => by
    have ih := blk_ms τ d fun j => z (j.succ : Fin (d.len + 1))
    refine Eq.trans ?_ (Fin.sum_univ_succ (n := d.len) _).symm
    unfold msOf at ih ⊢
    rw [map_addCases]
    congr 1
    · rw [Multiset.map_map]
      refine Multiset.map_congr rfl fun i _ => ?_
      have h1 : (Dat.cons b d).idx (Fin.castAdd _ i) = (0 : Fin (d.len + 1)) :=
        Fin.addCases_left (motive := fun _ => Fin (d.len + 1)) (left := fun _ => 0) (right := fun i => (d.idx i).succ) i
      have h2 : (Dat.cons b d).lam τ (Fin.castAdd _ i) = b.Λ τ i :=
        Fin.addCases_left (motive := fun _ => ℂ) (left := b.Λ τ) (right := d.lam τ) i
      exact congrArg₂ (· + ·) h2 (congrArg z h1)
    · refine Eq.trans ?_ ih
      refine Multiset.map_congr rfl fun i _ => ?_
      have h1 : (Dat.cons b d).idx (Fin.natAdd _ i) = ((d.idx i).succ : Fin (d.len + 1)) :=
        Fin.addCases_right (motive := fun _ => Fin (d.len + 1)) (left := fun _ => 0) (right := fun i => (d.idx i).succ) i
      have h2 : (Dat.cons b d).lam τ (Fin.natAdd _ i) = d.lam τ i :=
        Fin.addCases_right (motive := fun _ => ℂ) (left := b.Λ τ) (right := d.lam τ) i
      exact congrArg₂ (· + ·) h2 (congrArg z h1)

theorem main (n : ℕ) (d : Dat S n) (h2 : 2 ≤ d.len) : ∃ b : Datum E n, ∀ z, b.Pt S (msOf (d.ptL z)) (d.ptS z) := by
  choose V hV hA using fun j => blo_at (blk d j).2
  refine ⟨⟨d.len, h2, fun j => (blk d j).1, fun j => (blk d j).2.pos, blk_sum d, fun j => mu1 E _, V, hV⟩, fun z => ?_⟩
  refine ⟨z, _, _, hA, fun τ => blk_ms τ d z, fun w _ => ?_⟩
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [blk_sat, Multiset.map_map]
  rfl

end UpperTheory.ConvolutionTheory.BW.BlockSaturationData

theorem UpperTheory.ConvolutionTheory.BW.datDatum :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E], UpperTheory.ConvolutionTheory.BW.DatDatum E := by
  intro E _ _ _ S n d h2
  obtain ⟨b, hb⟩ := UpperTheory.ConvolutionTheory.BW.BlockSaturationData.main n d h2
  exact ⟨b, ⟨_, _, hb 0⟩, fun F _ hF z => hF _ _ (hb z)⟩
